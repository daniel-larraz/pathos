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

theorem case_0_eo__24is_5fcons_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fcons_5fapp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_cons_app.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__is_cons_app.case_0 x_a0 = some (__is_cons_app y0)
      | core.result.Result.Ok none => EoCases.__is_cons_app.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fcons_5fapp
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_cons_app.case_0
  case_again hinv hG with h_v1 in EoCases.__is_cons_app.case_0 using hn_a0 hn_v1 hn_v2

theorem case_1_eo__24is_5fcons_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fcons_5fapp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_cons_app.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__is_cons_app.case_1 x_a0 = some (__is_cons_app y0)
      | core.result.Result.Ok none => EoCases.__is_cons_app.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fcons_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_eq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 dropping h_v0 he_v1 hinv1 e_v1 s1 v0
  have h_ite_v9 := (show if_1_eo__24is_5fcons_5fapp s2 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24is_5fcons_5fapp
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 dropping h_v1 v1
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo_tuple_2eunit.construct s2 e_v3 (by rw [he_v3]; exact empty_args) hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 dropping h_v1 he_v3 e_v3 v1
      step as ⟨e_v4, he_v4⟩
      store_step with Store.builtin_spec_is_eq s3 e_v4 (by rw [he_v4]; rfl) h_a0 h_v3 hinv3 h64 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying h_a0 dropping h_v3 he_v4 e_v4 v3
      have h_ite_v8 := (show if_0_eo__24is_5fcons_5fapp s4 v4 a0 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24is_5fcons_5fapp
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
        · ite_branch hbv_5
          store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v5, s5, hinv5, h_v5⟩ growing hG carrying h_a0 dropping h_v4 v4
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_5 h_v5)
        · ite_branch hbv_5
          store_step with ih.eo__24eo_5fdt_5fselectors s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_a0 h_v4 v4
          step as ⟨e_v7, he_v7⟩
          store_step with Store.builtin_spec_is_ok s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying dropping h_v6 he_v7 e_v7 v6
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_5 h_v7)
        · ite_branch hbv_5
          ite_stuck hinv4 hG with hx_5)
      store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_a0 h_ite_v8 h_v4 hinv4 s4 v4
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_2 h_v8)
    · ite_branch hbv_2
      ite_stuck hinv2 hG with hx_2)
  store_step with h_ite_v9 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying dropping h_a0 h_ite_v9 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v9 in EoCases.__is_cons_app.case_1 using hn_a0

/-- logos's `__is_cons_app` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fcons_5fapp.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __is_cons_app x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_cons_app.case_0 x_a0, EoCases.__is_cons_app.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __is_cons_app
  unfold EoCases.__is_cons_app.case_0 EoCases.__is_cons_app.case_1
  logos_eq

theorem step_eo__24is_5fcons_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24is_5fcons_5fapp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__is_cons_app x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __is_cons_app x_a0 = __is_cons_app y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fcons_5fapp.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24is_5fcons_5fapp
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  round_step with case_0_eo__24is_5fcons_5fapp_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using hn_a0
  round_step with case_1_eo__24is_5fcons_5fapp_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hn_a0 hc0
  round_stuck hinv3 hG using hn_a0 hc0 hc1 in EoCases.__is_cons_app.case_0 EoCases.__is_cons_app.case_1

theorem body_eo__24is_5fcons_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24is_5fcons_5fapp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_cons_app x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24is_5fcons_5fapp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_cons_app x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24is_5fcons_5fapp body_eo__24is_5fcons_5fapp_loop
  step with step_eo__24is_5fcons_5fapp_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24is_5fcons_5fapp at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24is_5fcons_5fapp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fcons_5fapp.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24is_5fcons_5fapp
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 904#u32 _ [a0] rfl
    (fun s1 => body_eo__24is_5fcons_5fapp s1 a0) (fun s' t => Represents.rep s' t (__is_cons_app x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_904 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_904 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fcons_5fapp_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5feq_5fmaybe_5fto_5freal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5feq_5fmaybe_5fto_5freal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_eq_maybe_to_real.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_eq_maybe_to_real.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5feq_5fmaybe_5fto_5freal
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__is_eq_maybe_to_real.case_0
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__is_eq_maybe_to_real.case_0 using hn_a0 hn_a1

theorem case_1_eo__24is_5feq_5fmaybe_5fto_5freal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5feq_5fmaybe_5fto_5freal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_eq_maybe_to_real.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_eq_maybe_to_real.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5feq_5fmaybe_5fto_5freal
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_eq_maybe_to_real.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_to_5freal.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__is_eq_maybe_to_real.case_1
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__is_eq_maybe_to_real.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_a1 h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  case_done hinv2 hG with h_v4 in EoCases.__is_eq_maybe_to_real.case_1 using hn_a0 hn_a1 hn_v1 hn_v2

/-- logos's fall-through helpers of `__is_eq_maybe_to_real`, each the program's cases from its first on. -/
theorem eo__24is_5feq_5fmaybe_5fto_5freal.helper_1 (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___is_eq_maybe_to_real x_a0 x_a1 =
      firstSome [EoCases.__is_eq_maybe_to_real.case_1 x_a0 x_a1] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___is_eq_maybe_to_real
  unfold EoCases.__is_eq_maybe_to_real.case_1
  logos_eq_deep

/-- logos's `__is_eq_maybe_to_real` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5feq_5fmaybe_5fto_5freal.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __is_eq_maybe_to_real x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_eq_maybe_to_real.case_0 x_a0 x_a1, EoCases.__is_eq_maybe_to_real.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __is_eq_maybe_to_real
  unfold EoCases.__is_eq_maybe_to_real.case_0
  have hn := eo__24is_5feq_5fmaybe_5fto_5freal.helper_1
  logos_eq_deep

theorem body_eo__24is_5feq_5fmaybe_5fto_5freal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24is_5feq_5fmaybe_5fto_5freal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_eq_maybe_to_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5feq_5fmaybe_5fto_5freal.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24is_5feq_5fmaybe_5fto_5freal
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24is_5feq_5fmaybe_5fto_5freal_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24is_5feq_5fmaybe_5fto_5freal_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__is_eq_maybe_to_real.case_0 EoCases.__is_eq_maybe_to_real.case_1

theorem eo__24is_5feq_5fmaybe_5fto_5freal_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5feq_5fmaybe_5fto_5freal.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24is_5feq_5fmaybe_5fto_5freal
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24is_5feq_5fmaybe_5fto_5freal s1 a0 a1) (fun s' t => Represents.rep s' t (__is_eq_maybe_to_real x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5feq_5fmaybe_5fto_5freal_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5finstantiation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5finstantiation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_instantiation.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_instantiation.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5finstantiation
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__is_instantiation.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__is_instantiation.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__is_instantiation.case_0 using hn_a0 hn_a1

theorem case_1_eo__24is_5finstantiation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5finstantiation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_instantiation.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_instantiation.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5finstantiation
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_instantiation.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_instantiation.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_instantiation.case_1
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__is_instantiation.case_1
  obtain ⟨hn_v8, hn_v9⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv1 h_v5
  pat_unapply h_a1 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_instantiation.case_1
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__is_instantiation.case_1
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v16 (by rw [he_v16]; exact empty_args) hinv1 h64 as ⟨v16, s2, hinv2, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 h_v14 h_v15 dropping h_a1 h_v11 h_v4 h_v5 h_v6 h_v8 he_v16 hinv1 e_v16 s1 v11 v4 v5 v6 v8
  pat_same v14 v16 with h_v14 h_v16 using hinv2 else hinv2 hG in EoCases.__is_instantiation.case_1
  store_step with ih.eo__24eo_5ftypeof s2 v15 _ hinv2 h64 (hG.rem hrem) h_v15 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 h_v15 h_v16 hinv2 s2 v14 v15 v16
  have h_req_v19 := (show requires_0_eo__24is_5finstantiation s3 v17 v9 v2 v12 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24is_5finstantiation
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v17 v9 with h_v17 h_v9 using hinv3 hG
    req_stuck h_v17 as hq_v17 using hinv3 hG
    store_step with ih.eo__24is_5finstantiation s3 v2 v12 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v12 as ⟨v18, s4, hinv4, h_v18⟩ growing hG carrying dropping h_v12 h_v17 h_v2 h_v9 hinv3 s3 v12 v17 v2 v9
    req_done hinv4 hG with h_v18 using hq_v17)
  store_step with h_req_v19 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying dropping h_req_v19 h_v12 h_v17 h_v2 h_v9 hinv3 s3 v12 v17 v2 v9
  case_done hinv5 hG with h_v19 in EoCases.__is_instantiation.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v14 hn_v15

/-- logos's `__is_instantiation` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5finstantiation.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __is_instantiation x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_instantiation.case_0 x_a0 x_a1, EoCases.__is_instantiation.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __is_instantiation
  unfold EoCases.__is_instantiation.case_0 EoCases.__is_instantiation.case_1
  logos_eq

theorem body_eo__24is_5finstantiation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24is_5finstantiation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_instantiation x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5finstantiation.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24is_5finstantiation
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24is_5finstantiation_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24is_5finstantiation_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__is_instantiation.case_0 EoCases.__is_instantiation.case_1

theorem eo__24is_5finstantiation_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5finstantiation.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24is_5finstantiation
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 906#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24is_5finstantiation s1 a0 a1) (fun s' t => Represents.rep s' t (__is_instantiation x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_906 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_906 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5finstantiation_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_to_q s e_v6 (by rw [he_v6]; rfl) h_v5 hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 dropping hinv1 s1
  replace h_v8 := Represents.rep_of_eq h_v8 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_eq s2 e_v9 (by rw [he_v9]; rfl) h_v6 h_v8 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 h_v8 he_v9 hinv2 e_v9 s2 v6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_to_q s3 e_v10 (by rw [he_v10]; rfl) h_v2 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v2 h_v4 h_v5 h_v9 dropping he_v10 hinv3 e_v10 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s4 _ hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v2 h_v4 h_v5 h_v9 h_v10 dropping hinv4 s4
  replace h_v12 := Represents.rep_of_eq h_v12 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v13, he_v13⟩
  store_step with Store.builtin_spec_eq s5 e_v13 (by rw [he_v13]; rfl) h_v10 h_v12 hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v2 h_v4 h_v5 h_v9 dropping h_v10 h_v12 he_v13 hinv5 e_v13 s5 v10 v12
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_or s6 e_v14 (by rw [he_v14]; rfl) h_v9 h_v13 hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v13 h_v9 he_v14 hinv6 e_v14 s6 v13 v9
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_not s7 e_v15 (by rw [he_v15]; rfl) h_v14 hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v14 he_v15 hinv7 e_v15 s7 v14
  store_step with Store.apply_rep s8 v4 v5 _ _ hinv8 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v2 h_v15 dropping h_v4 h_v5 hinv8 s8 v4 v5
  store_step with Store.apply_rep s9 v16 v2 _ _ hinv9 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying h_v15 dropping h_v16 h_v2 hinv9 s9 v16 v2
  store_step with ih.eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s10 v17 _ hinv10 h64 (hG.rem hrem) h_v17 as ⟨v18, s11, hinv11, h_v18⟩ growing hG carrying h_v15 dropping h_v17 hinv10 s10 v17
  step as ⟨e_v19, he_v19⟩
  store_step with Store.builtin_spec_and s11 e_v19 (by rw [he_v19]; rfl) h_v15 h_v18 hinv11 h64 as ⟨v19, s12, hinv12, h_v19⟩ growing hG carrying dropping h_v15 h_v18 he_v19 hinv11 e_v19 s11 v15 v18
  case_done hinv12 hG with h_v19 in EoCases.__is_poly_norm_rel_consts.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__is_poly_norm_rel_consts` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fpoly_5fnorm_5frel_5fconsts.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __is_poly_norm_rel_consts x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_poly_norm_rel_consts.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __is_poly_norm_rel_consts
  unfold EoCases.__is_poly_norm_rel_consts.case_0
  logos_eq

theorem body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24is_5fpoly_5fnorm_5frel_5fconsts s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_poly_norm_rel_consts x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fpoly_5fnorm_5frel_5fconsts.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24is_5fpoly_5fnorm_5frel_5fconsts
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__is_poly_norm_rel_consts.case_0

theorem eo__24is_5fpoly_5fnorm_5frel_5fconsts_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fpoly_5fnorm_5frel_5fconsts.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24is_5fpoly_5fnorm_5frel_5fconsts
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24is_5fpoly_5fnorm_5frel_5fconsts s1 a0) (fun s' t => Represents.rep s' t (__is_poly_norm_rel_consts x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  have h_ite_v14 := (show if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_v7 v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_v2 dropping h_v5 h_v7 he_v9 e_v9 v5 v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v2 dropping h_v9 he_v10 e_v10 v9
      have h_ite_v13 := (show if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 dropping h_ite_v13 h_v10 v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 dropping h_ite_v14 h_v5 h_v7 hinv2 s2 v5 v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v14 dropping he_v15 hinv3 e_v15 s3
  have h_ite_v22 := (show if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v14 dropping h_v15 v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_v14 dropping h_v15 h_v2 he_v17 e_v17 v15 v2
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_v14 dropping h_v17 he_v18 e_v18 v17
      have h_ite_v21 := (show if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v14 dropping h_ite_v21 h_v18 v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v14 dropping h_ite_v22 h_v15 h_v2 hinv4 s4 v15 v2
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying dropping h_v14 h_v22 he_v23 hinv5 e_v23 s5 v14 v22
  case_done hinv6 hG with h_v23 in EoCases.__is_poly_norm_rel_consts_rel.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  have h_ite_v14 := (show if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_v7 v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_v2 dropping h_v5 h_v7 he_v9 e_v9 v5 v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v2 dropping h_v9 he_v10 e_v10 v9
      have h_ite_v13 := (show if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 dropping h_ite_v13 h_v10 v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 dropping h_ite_v14 h_v5 h_v7 hinv2 s2 v5 v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v14 dropping he_v15 hinv3 e_v15 s3
  have h_ite_v22 := (show if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v14 dropping h_v15 v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_v14 dropping h_v15 h_v2 he_v17 e_v17 v15 v2
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_v14 dropping h_v17 he_v18 e_v18 v17
      have h_ite_v21 := (show if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v14 dropping h_ite_v21 h_v18 v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v14 dropping h_ite_v22 h_v15 h_v2 hinv4 s4 v15 v2
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying dropping h_v14 h_v22 he_v23 hinv5 e_v23 s5 v14 v22
  case_done hinv6 hG with h_v23 in EoCases.__is_poly_norm_rel_consts_rel.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v4 dropping h_a0 h_v1 h_v2 h_v5 he_v6 e_v6 v1 v2 v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_2
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying dropping h_v4 h_v6 hinv1 s1 v4 v6
  case_done hinv2 hG with h_v7 in EoCases.__is_poly_norm_rel_consts_rel.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_3
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_3
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_3
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  have h_ite_v14 := (show if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_v7 v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_v2 dropping h_v5 h_v7 he_v9 e_v9 v5 v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v2 dropping h_v9 he_v10 e_v10 v9
      have h_ite_v13 := (show if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 dropping h_ite_v13 h_v10 v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 dropping h_ite_v14 h_v5 h_v7 hinv2 s2 v5 v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v14 dropping he_v15 hinv3 e_v15 s3
  have h_ite_v22 := (show if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v14 dropping h_v15 v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_v14 dropping h_v15 h_v2 he_v17 e_v17 v15 v2
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_v14 dropping h_v17 he_v18 e_v18 v17
      have h_ite_v21 := (show if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v14 dropping h_ite_v21 h_v18 v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v14 dropping h_ite_v22 h_v15 h_v2 hinv4 s4 v15 v2
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying dropping h_v14 h_v22 he_v23 hinv5 e_v23 s5 v14 v22
  case_done hinv6 hG with h_v23 in EoCases.__is_poly_norm_rel_consts_rel.case_3 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_4
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts_rel.case_4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_4
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  have h_ite_v14 := (show if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_v7 v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_v2 dropping h_v5 h_v7 he_v9 e_v9 v5 v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v2 dropping h_v9 he_v10 e_v10 v9
      have h_ite_v13 := (show if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v2 dropping h_v10 v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 dropping h_ite_v13 h_v10 v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 dropping h_ite_v14 h_v5 h_v7 hinv2 s2 v5 v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v14 dropping he_v15 hinv3 e_v15 s3
  have h_ite_v22 := (show if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v14 dropping h_v15 v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_v14 dropping h_v15 h_v2 he_v17 e_v17 v15 v2
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_v14 dropping h_v17 he_v18 e_v18 v17
      have h_ite_v21 := (show if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v14 dropping h_v18 v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v14 dropping h_ite_v21 h_v18 v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v14 dropping h_ite_v22 h_v15 h_v2 hinv4 s4 v15 v2
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying dropping h_v14 h_v22 he_v23 hinv5 e_v23 s5 v14 v22
  case_done hinv6 hG with h_v23 in EoCases.__is_poly_norm_rel_consts_rel.case_4 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping
  case_done hinv1 hG with h_v0 in EoCases.__is_poly_norm_rel_consts_rel.case_5 using hn_a0

theorem cases_0_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0 = none ∧ EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0 = none ∧ EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0 = none ∧ EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] = [] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] = [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] = [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] = [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0 = none ∧ EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] = [] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] = [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__is_poly_norm_rel_consts_rel` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __is_poly_norm_rel_consts_rel x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __is_poly_norm_rel_consts_rel
  unfold EoCases.__is_poly_norm_rel_consts_rel.case_0 EoCases.__is_poly_norm_rel_consts_rel.case_1 EoCases.__is_poly_norm_rel_consts_rel.case_2 EoCases.__is_poly_norm_rel_consts_rel.case_3 EoCases.__is_poly_norm_rel_consts_rel.case_4 EoCases.__is_poly_norm_rel_consts_rel.case_5
  logos_eq

theorem body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_poly_norm_rel_consts_rel x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_0_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] = [] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  body_group_step with cases_0_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] = [EoCases.__is_poly_norm_rel_consts_rel.case_0 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_1 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_2 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_3 x_a0] ++ [EoCases.__is_poly_norm_rel_consts_rel.case_4 x_a0, EoCases.__is_poly_norm_rel_consts_rel.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__is_poly_norm_rel_consts_rel.case_0 EoCases.__is_poly_norm_rel_consts_rel.case_1 EoCases.__is_poly_norm_rel_consts_rel.case_2 EoCases.__is_poly_norm_rel_consts_rel.case_3 EoCases.__is_poly_norm_rel_consts_rel.case_4 EoCases.__is_poly_norm_rel_consts_rel.case_5

theorem eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s1 a0) (fun s' t => Represents.rep s' t (__is_poly_norm_rel_consts_rel x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fquant_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fquant_5fdt_5fsplit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fquant_5fdt_5fsplit
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split.case_0
  pat_unapply h_a4 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_and.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a2 h_a3 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a4 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split.case_0
  store_step with ih.eo__24is_5fquant_5fdt_5fsplit_5fconj s2 a0 v5 a2 a3 v12 _ _ _ _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v5 h_a2 h_a3 h_v12 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a2 h_a3 h_v2 h_v9 dropping h_v11 h_v12 h_v13 h_v5 hinv2 s2 v11 v12 v13 v5
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a2 h_a3 h_v2 h_v9 h_v14 dropping hinv3 s3
  have h_req_v17 := (show requires_0_eo__24is_5fquant_5fdt_5fsplit s4 v14 v15 a0 v2 a2 a3 v9 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24is_5fquant_5fdt_5fsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v14 v15 with h_v14 h_v15 using hinv4 hG
    req_stuck h_v14 as hq_v14 using hinv4 hG
    store_step with ih.eo__24is_5fquant_5fdt_5fsplit s4 a0 v2 a2 a3 v9 _ _ _ _ _ hinv4 h64 (hG.rem hrem) h_a0 h_v2 h_a2 h_a3 h_v9 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying dropping h_a0 h_a2 h_a3 h_v14 h_v15 h_v2 h_v9 hinv4 s4 v14 v15 v2 v9
    req_done hinv5 hG with h_v16 using hq_v14)
  store_step with h_req_v17 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying dropping h_a0 h_a2 h_a3 h_req_v17 h_v14 h_v15 h_v2 h_v9 hinv4 s4 v14 v15 v2 v9
  case_done hinv6 hG with h_v17 in EoCases.__is_quant_dt_split.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24is_5fquant_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fquant_5fdt_5fsplit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fquant_5fdt_5fsplit
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a1 h_a4 dropping he_v0 e_v0
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a4 dropping h_a1 h_v0 hinv1 s1 v0
  pat_same a4 v1 with h_a4 h_v1 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split.case_1
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a4 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__is_quant_dt_split.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

theorem case_2_eo__24is_5fquant_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_2_eo__24is_5fquant_5fdt_5fsplit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24is_5fquant_5fdt_5fsplit
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a2 h_a3 h_a4 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  have h_req_v9 := (show requires_1_eo__24is_5fquant_5fdt_5fsplit s2 v2 v7 a0 v5 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24is_5fquant_5fdt_5fsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v2 v7 with h_v2 h_v7 using hinv2 hG
    req_stuck h_v2 as hq_v2 using hinv2 hG
    store_step with ih.eo__24is_5fquant_5fdt_5fsplit_5fconj s2 a0 v5 a2 a3 a4 _ _ _ _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v5 h_a2 h_a3 h_a4 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_a0 h_a2 h_a3 h_a4 h_v2 h_v5 h_v7 hinv2 s2 v2 v5 v7
    req_done hinv3 hG with h_v8 using hq_v2)
  store_step with h_req_v9 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_req_v9 h_v2 h_v5 h_v7 hinv2 s2 v2 v5 v7
  case_done hinv4 hG with h_v9 in EoCases.__is_quant_dt_split.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__is_quant_dt_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fquant_5fdt_5fsplit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __is_quant_dt_split x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_quant_dt_split.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split.case_2 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __is_quant_dt_split
  unfold EoCases.__is_quant_dt_split.case_0 EoCases.__is_quant_dt_split.case_1 EoCases.__is_quant_dt_split.case_2
  logos_eq

theorem body_eo__24is_5fquant_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24is_5fquant_5fdt_5fsplit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_quant_dt_split x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fquant_5fdt_5fsplit.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24is_5fquant_5fdt_5fsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24is_5fquant_5fdt_5fsplit_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  case_step with case_1_eo__24is_5fquant_5fdt_5fsplit_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  case_step with case_2_eo__24is_5fquant_5fdt_5fsplit_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2 in EoCases.__is_quant_dt_split.case_0 EoCases.__is_quant_dt_split.case_1 EoCases.__is_quant_dt_split.case_2

theorem eo__24is_5fquant_5fdt_5fsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fquant_5fdt_5fsplit.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24is_5fquant_5fdt_5fsplit
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 909#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24is_5fquant_5fdt_5fsplit s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__is_quant_dt_split x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_909 hsem
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
      exact ProgramSem.to_909 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fquant_5fdt_5fsplit_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v2 h_v4 h_v5 dropping h_a2 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_a4 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a4 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v5 h_v9 h_v16 h_v18 h_v19 dropping h_v11 h_v12 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v12 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_same v19 v5 with h_v19 h_v5 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v5 h_v9 h_v16 dropping h_v18 h_v19 h_v20 he_v21 hinv3 e_v21 s3 v18 v19 v20
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s4 e_v22 (by rw [he_v22]; rfl) h_v21 h_v16 h_v5 hinv4 h64 (hG.rem hrem) (by not_left_tac) as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 h_v16 dropping h_v21 h_v5 he_v22 hinv4 e_v22 s4 v21 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s5 1#u32 (-1) (by scalar_tac) hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 h_v16 h_v22 dropping hinv5 s5
  have h_req_v28 := (show requires_0_eo__24is_5fquant_5fdt_5fsplit_5fconj s6 v22 v23 v16 v9 a0 a1 v2 a3 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v22 v23 with h_v22 h_v23 using hinv6 hG
    req_stuck h_v22 as hq_v22 using hinv6 hG
    step as ⟨e_v24, he_v24⟩
    store_step with CtorSpec.eo_forall.construct s6 e_v24 (by rw [he_v24]; exact empty_args) hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 h_v16 dropping h_v22 h_v23 he_v24 hinv6 e_v24 s6 v22 v23
    store_step with Store.apply_rep s7 v24 v16 _ _ hinv7 h64 h_v24 h_v16 (by ns_tac) (by ns_tac) as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 dropping h_v16 h_v24 hinv7 s7 v16 v24
    store_step with Store.apply_rep s8 v25 v9 _ _ hinv8 h64 h_v25 h_v9 (by ns_tac) (by ns_tac) as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 dropping h_v25 h_v9 hinv8 s8 v25 v9
    store_step with ih.eo__24is_5fquant_5fdt_5fsplit_5fconj s9 a0 a1 v2 a3 v26 _ _ _ _ _ hinv9 h64 (hG.rem hrem) h_a0 h_a1 h_v2 h_a3 h_v26 as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying dropping h_a0 h_a1 h_a3 h_v2 h_v26 hinv9 s9 v2 v26
    req_done hinv10 hG with h_v27 using hq_v22)
  store_step with h_req_v28 as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying dropping h_req_v28 h_v16 h_v2 h_v22 h_v23 h_v9 hinv6 s6 v16 v2 v22 v23 v9
  case_done hinv11 hG with h_v28 in EoCases.__is_quant_dt_split_conj.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

theorem case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_a4 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v5 h_v6 dropping h_a2 h_a4 h_v0 h_v2 he_v7 hinv1 e_v7 s1 v0 v2
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v12 h_v13 dropping h_v5 h_v6 h_v7 h_v9 he_v14 hinv2 e_v14 s2 v5 v6 v7 v9
  pat_same v12 v14 with h_v12 h_v14 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_1
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v12 h_v14 he_v15 hinv3 e_v15 s3 v12 v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s4 e_v16 (by rw [he_v16]; rfl) h_v15 h_v10 h_v13 hinv4 h64 (hG.rem hrem) (by not_left_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v15 he_v16 hinv4 e_v16 s4 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s5 1#u32 (-1) (by scalar_tac) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v16 dropping hinv5 s5
  have h_req_v32 := (show requires_3_eo__24is_5fquant_5fdt_5fsplit_5fconj s6 v16 v17 v13 a3 a1 v10 v3 a0 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_3_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v16 v17 with h_v16 h_v17 using hinv6 hG
    req_stuck h_v16 as hq_v16 using hinv6 hG
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s6 e_v18 (by rw [he_v18]; exact empty_args) hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v16 h_v17 he_v18 hinv6 e_v18 s6 v16 v17
    store_step with Store.apply_rep s7 v18 v13 _ _ hinv7 h64 h_v18 h_v13 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v18 hinv7 s7 v18
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v19 dropping he_v20 hinv8 e_v20 s8
    store_step with Store.apply_rep s9 v19 v20 _ _ hinv9 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v19 h_v20 hinv9 s9 v19 v20
    step as ⟨e_v22, he_v22⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s10 e_v22 (by rw [he_v22]; exact empty_args) hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v21 dropping he_v22 hinv10 e_v22 s10
    store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s11 a3 v21 v22 _ _ _ hinv11 h64 (hG.rem hrem) h_a3 h_v21 h_v22 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v21 h_v22 hinv11 s11 v21 v22
    store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v23 dropping hinv12 s12
    have h_req_v31 := (show requires_2_eo__24is_5fquant_5fdt_5fsplit_5fconj s13 v23 v24 a1 v13 v10 v3 a0 a3 ⦃ r s' => s'.Inv ∧ s13.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_2_eo__24is_5fquant_5fdt_5fsplit_5fconj
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s13
      req_same v23 v24 with h_v23 h_v24 using hinv13 hG
      req_stuck h_v23 as hq_v23 using hinv13 hG
      store_step with Store.apply_rep s13 a1 v13 _ _ hinv13 h64 h_a1 h_v13 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a3 h_v3 h_v10 dropping h_a1 h_v13 h_v23 h_v24 hinv13 s13 v13 v23 v24
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s14 e_v26 (by rw [he_v26]; exact empty_args) hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_a0 h_a3 h_v3 h_v10 h_v25 dropping he_v26 hinv14 e_v26 s14
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo_forall.construct s15 e_v27 (by rw [he_v27]; exact empty_args) hinv15 h64 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_a0 h_a3 h_v3 h_v10 h_v25 h_v26 dropping he_v27 hinv15 e_v27 s15
      store_step with Store.apply_rep s16 v27 v10 _ _ hinv16 h64 h_v27 h_v10 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_a0 h_a3 h_v3 h_v25 h_v26 dropping h_v10 h_v27 hinv16 s16 v10 v27
      store_step with Store.apply_rep s17 v28 v3 _ _ hinv17 h64 h_v28 h_v3 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_a3 h_v25 h_v26 dropping h_v28 h_v3 hinv17 s17 v28 v3
      store_step with ih.eo__24is_5fquant_5fdt_5fsplit_5fconj s18 a0 v25 v26 a3 v29 _ _ _ _ _ hinv18 h64 (hG.rem hrem) h_a0 h_v25 h_v26 h_a3 h_v29 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying dropping h_a0 h_a3 h_v25 h_v26 h_v29 hinv18 s18 v25 v26 v29
      req_done hinv19 hG with h_v30 using hq_v23)
    store_step with h_req_v31 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying dropping h_a3 h_req_v31 h_v10 h_v13 h_v23 h_v24 h_v3 hinv13 s13 v10 v13 v23 v24 v3
    req_done hinv20 hG with h_v31 using hq_v16)
  store_step with h_req_v32 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying dropping h_req_v32 h_v10 h_v13 h_v16 h_v17 h_v3 hinv6 s6 v10 v13 v16 v17 v3
  case_done hinv21 hG with h_v32 in EoCases.__is_quant_dt_split_conj.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v2 hn_v3 hn_v5 hn_v6 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_2
  pat_unapply h_a4 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_2
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v5 h_v6 dropping h_a2 h_a4 h_v0 h_v2 he_v7 hinv1 e_v7 s1 v0 v2
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_2
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v6 dropping h_v5 h_v7 he_v8 hinv2 e_v8 s2 v5 v7
  pat_same v6 v8 with h_v6 h_v8 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_2
  store_step with ih.eo__24eo_5ftypeof s3 a1 _ hinv3 h64 (hG.rem hrem) h_a1 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 dropping h_v6 h_v8 hinv3 s3 v6 v8
  store_step with ih.eo__24eo_5ftypeof s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v9 dropping hinv4 s4
  have h_req_v23 := (show requires_5_eo__24is_5fquant_5fdt_5fsplit_5fconj s5 v9 v10 a0 a1 a3 v3 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_5_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v9 v10 with h_v9 h_v10 using hinv5 hG
    req_stuck h_v9 as hq_v9 using hinv5 hG
    store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 dropping h_v10 h_v9 hinv5 s5 v10 v9
    step as ⟨e_v12, he_v12⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v11 dropping he_v12 hinv6 e_v12 s6
    store_step with Store.apply_rep s7 v12 a0 _ _ hinv7 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 dropping h_a0 h_v12 hinv7 s7 v12
    step as ⟨e_v14, he_v14⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 h_v13 dropping he_v14 hinv8 e_v14 s8
    store_step with Store.apply_rep s9 v13 v14 _ _ hinv9 h64 h_v13 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 dropping h_v13 h_v14 hinv9 s9 v13 v14
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 h_v15 dropping he_v16 hinv10 e_v16 s10
    store_step with Store.apply_rep s11 v16 a1 _ _ hinv11 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 dropping h_a1 h_v16 hinv11 s11 v16
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 h_v17 dropping he_v18 hinv12 e_v18 s12
    store_step with Store.apply_rep s13 v17 v18 _ _ hinv13 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 dropping h_v17 h_v18 hinv13 s13 v17 v18
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 h_v19 dropping he_v20 hinv14 e_v20 s14
    store_step with ih.eo__24substitute_5fsimul_5frec s15 v11 a3 v15 v19 v20 _ _ _ _ _ hinv15 h64 (hG.rem hrem) h_v11 h_a3 h_v15 h_v19 h_v20 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v3 dropping h_a3 h_v11 h_v15 h_v19 h_v20 hinv15 s15 v11 v15 v19 v20
    step as ⟨e_v22, he_v22⟩
    store_step with Store.builtin_spec_eq s16 e_v22 (by rw [he_v22]; rfl) h_v21 h_v3 hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying dropping h_v21 h_v3 he_v22 hinv16 e_v22 s16 v21 v3
    req_done hinv17 hG with h_v22 using hq_v9)
  store_step with h_req_v23 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying dropping h_a0 h_a1 h_req_v23 h_v10 h_v3 h_v9 hinv5 s5 v10 v3 v9
  case_done hinv18 hG with h_v23 in EoCases.__is_quant_dt_split_conj.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v2 hn_v3 hn_v5 hn_v6

theorem case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_3
  store_step with ih.eo__24eo_5ftypeof s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 dropping h_a2 h_v0 hinv1 s1 v0
  store_step with ih.eo__24eo_5ftypeof s2 a0 _ hinv2 h64 (hG.rem hrem) h_a0 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v1 dropping hinv2 s2
  have h_req_v15 := (show requires_6_eo__24is_5fquant_5fdt_5fsplit_5fconj s3 v1 v2 a0 a1 a3 a4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_6_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v1 v2 with h_v1 h_v2 using hinv3 hG
    req_stuck h_v1 as hq_v1 using hinv3 hG
    store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 dropping h_v1 h_v2 hinv3 s3 v1 v2
    step as ⟨e_v4, he_v4⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v3 dropping he_v4 hinv4 e_v4 s4
    store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 dropping h_a0 h_v4 hinv5 s5 v4
    step as ⟨e_v6, he_v6⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 h_v5 dropping he_v6 hinv6 e_v6 s6
    store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 dropping h_v5 h_v6 hinv7 s7 v5 v6
    step as ⟨e_v8, he_v8⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 h_v7 dropping he_v8 hinv8 e_v8 s8
    store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 dropping h_a1 h_v8 hinv9 s9 v8
    step as ⟨e_v10, he_v10⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 h_v9 dropping he_v10 hinv10 e_v10 s10
    store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 dropping h_v10 h_v9 hinv11 s11 v10 v9
    step as ⟨e_v12, he_v12⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 h_v11 dropping he_v12 hinv12 e_v12 s12
    store_step with ih.eo__24substitute_5fsimul_5frec s13 v3 a3 v7 v11 v12 _ _ _ _ _ hinv13 h64 (hG.rem hrem) h_v3 h_a3 h_v7 h_v11 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a4 dropping h_a3 h_v11 h_v12 h_v3 h_v7 hinv13 s13 v11 v12 v3 v7
    step as ⟨e_v14, he_v14⟩
    store_step with Store.builtin_spec_eq s14 e_v14 (by rw [he_v14]; rfl) h_v13 h_a4 hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_a4 h_v13 he_v14 hinv14 e_v14 s14 v13
    req_done hinv15 hG with h_v14 using hq_v1)
  store_step with h_req_v15 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying dropping h_a0 h_a1 h_req_v15 h_v1 h_v2 hinv3 s3 v1 v2
  case_done hinv16 hG with h_v15 in EoCases.__is_quant_dt_split_conj.case_3 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

/-- logos's fall-through helpers of `__is_quant_dt_split_conj`, each the program's cases from its first on. -/
theorem eo__24is_5fquant_5fdt_5fsplit_5fconj.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4 =
      firstSome [EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___is_quant_dt_split_conj
  unfold EoCases.__is_quant_dt_split_conj.case_1 EoCases.__is_quant_dt_split_conj.case_2 EoCases.__is_quant_dt_split_conj.case_3
  logos_eq_deep

/-- logos's `__is_quant_dt_split_conj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fquant_5fdt_5fsplit_5fconj.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_quant_dt_split_conj.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __is_quant_dt_split_conj
  unfold EoCases.__is_quant_dt_split_conj.case_0
  have hn := eo__24is_5fquant_5fdt_5fsplit_5fconj.helper_1
  logos_eq_deep

theorem body_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fquant_5fdt_5fsplit_5fconj.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  case_step with case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  case_step with case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1
  case_step with case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s3 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2 hc3 in EoCases.__is_quant_dt_split_conj.case_0 EoCases.__is_quant_dt_split_conj.case_1 EoCases.__is_quant_dt_split_conj.case_2 EoCases.__is_quant_dt_split_conj.case_3

theorem eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fquant_5fdt_5fsplit_5fconj.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24is_5fquant_5fdt_5fsplit_5fconj
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 910#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24is_5fquant_5fdt_5fsplit_5fconj s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_910 hsem
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
      exact ProgramSem.to_910 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_miniscope_or.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_miniscope_or.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_or.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_0
  pat_unapply h_a2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_0
  pat_same v12 v5 with h_v12 h_v5 using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 dropping h_v11 h_v12 h_v13 he_v14 hinv2 e_v14 s2 v11 v12 v13
  store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s3 v5 a0 v14 _ _ _ hinv3 h64 (hG.rem hrem) h_v5 h_a0 h_v14 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v2 h_v9 dropping h_v14 h_v5 hinv3 s3 v14 v5
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v2 h_v9 h_v15 dropping hinv4 s4
  have h_req_v18 := (show requires_0_eo__24is_5fquant_5fminiscope_5for s5 v15 v16 a0 v2 v9 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24is_5fquant_5fminiscope_5for
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v15 v16 with h_v15 h_v16 using hinv5 hG
    req_stuck h_v15 as hq_v15 using hinv5 hG
    store_step with ih.eo__24is_5fquant_5fminiscope_5for s5 a0 v2 v9 _ _ _ hinv5 h64 (hG.rem hrem) h_a0 h_v2 h_v9 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying dropping h_a0 h_v15 h_v16 h_v2 h_v9 hinv5 s5 v15 v16 v2 v9
    req_done hinv6 hG with h_v17 using hq_v15)
  store_step with h_req_v18 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying dropping h_a0 h_req_v18 h_v15 h_v16 h_v2 h_v9 hinv5 s5 v15 v16 v2 v9
  case_done hinv7 hG with h_v18 in EoCases.__is_quant_miniscope_or.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_miniscope_or.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_miniscope_or.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_or.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_1
  pat_unapply h_a2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_1
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_1
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_1
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_forall.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v16 h_v18 h_v19 dropping h_v11 h_v12 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v12 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__is_quant_miniscope_or.case_1
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v16 h_v19 dropping h_v18 h_v20 he_v21 hinv3 e_v21 s3 v18 v20
  pat_same v19 v21 with h_v19 h_v21 using hinv4 else hinv4 hG in EoCases.__is_quant_miniscope_or.case_1
  pat_same v16 v5 with h_v16 h_v5 using hinv4 else hinv4 hG in EoCases.__is_quant_miniscope_or.case_1
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s4 e_v22 (by rw [he_v22]; exact empty_args) hinv4 h64 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 dropping h_v16 h_v19 h_v21 he_v22 hinv4 e_v22 s4 v16 v19 v21
  store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s5 v5 a0 v22 _ _ _ hinv5 h64 (hG.rem hrem) h_v5 h_a0 h_v22 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v2 h_v9 dropping h_v22 h_v5 hinv5 s5 v22 v5
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_v2 h_v9 h_v23 dropping hinv6 s6
  have h_req_v26 := (show requires_2_eo__24is_5fquant_5fminiscope_5for s7 v23 v24 a0 v2 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_2_eo__24is_5fquant_5fminiscope_5for
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v23 v24 with h_v23 h_v24 using hinv7 hG
    req_stuck h_v23 as hq_v23 using hinv7 hG
    store_step with ih.eo__24is_5fquant_5fminiscope_5for s7 a0 v2 v9 _ _ _ hinv7 h64 (hG.rem hrem) h_a0 h_v2 h_v9 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying dropping h_a0 h_v2 h_v23 h_v24 h_v9 hinv7 s7 v2 v23 v24 v9
    req_done hinv8 hG with h_v25 using hq_v23)
  store_step with h_req_v26 as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying dropping h_a0 h_req_v26 h_v2 h_v23 h_v24 h_v9 hinv7 s7 v2 v23 v24 v9
  case_done hinv9 hG with h_v26 in EoCases.__is_quant_miniscope_or.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

theorem case_2_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_miniscope_or.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a1 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_a2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_2
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v16 h_v18 h_v19 dropping h_a2 h_v11 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v19 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v22 as ⟨v25, v26, x_v25, x_v26, h_v25, h_v26, hn_v25, hn_v26⟩ using hinv3 else hinv3 hG in EoCases.__is_quant_miniscope_or.case_2
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_forall.construct s3 e_v27 (by rw [he_v27]; exact empty_args) hinv3 h64 as ⟨v27, s4, hinv4, h_v27⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v16 h_v23 h_v25 h_v26 dropping h_v18 h_v19 h_v20 h_v22 he_v27 hinv3 e_v27 s3 v18 v19 v20 v22
  pat_same v25 v27 with h_v25 h_v27 using hinv4 else hinv4 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v26 as ⟨v29, v30, x_v29, x_v30, h_v29, h_v30, hn_v29, hn_v30⟩ using hinv4 else hinv4 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_unapply h_v29 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv4 else hinv4 hG in EoCases.__is_quant_miniscope_or.case_2
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s4 e_v34 (by rw [he_v34]; exact empty_args) hinv4 h64 as ⟨v34, s5, hinv5, h_v34⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v16 h_v23 h_v30 h_v32 h_v33 dropping h_v25 h_v26 h_v27 h_v29 he_v34 hinv4 e_v34 s4 v25 v26 v27 v29
  pat_same v32 v34 with h_v32 h_v34 using hinv5 else hinv5 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_same v33 v5 with h_v33 h_v5 using hinv5 else hinv5 hG in EoCases.__is_quant_miniscope_or.case_2
  pat_same v23 v12 with h_v23 h_v12 using hinv5 else hinv5 hG in EoCases.__is_quant_miniscope_or.case_2
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s5 e_v35 (by rw [he_v35]; exact empty_args) hinv5 h64 as ⟨v35, s6, hinv6, h_v35⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v16 h_v30 dropping h_v23 h_v32 h_v33 h_v34 he_v35 hinv5 e_v35 s5 v23 v32 v33 v34
  store_step with Store.apply_rep s6 v35 v5 _ _ hinv6 h64 h_v35 h_v5 (by ns_tac) (by ns_tac) as ⟨v36, s7, hinv7, h_v36⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 dropping h_v35 h_v5 hinv6 s6 v35 v5
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s7 e_v37 (by rw [he_v37]; exact empty_args) hinv7 h64 as ⟨v37, s8, hinv8, h_v37⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 h_v36 dropping he_v37 hinv7 e_v37 s7
  store_step with Store.apply_rep s8 v36 v37 _ _ hinv8 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s9, hinv9, h_v38⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 dropping h_v36 h_v37 hinv8 s8 v36 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s9 e_v39 (by rw [he_v39]; exact empty_args) hinv9 h64 as ⟨v39, s10, hinv10, h_v39⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 h_v38 dropping he_v39 hinv9 e_v39 s9
  store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s10 v16 v38 v39 _ _ _ hinv10 h64 (hG.rem hrem) h_v16 h_v38 h_v39 as ⟨v40, s11, hinv11, h_v40⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 dropping h_v38 h_v39 hinv10 s10 v38 v39
  store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v41, s12, hinv12, h_v41⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 h_v40 dropping hinv11 s11
  have h_req_v52 := (show requires_4_eo__24is_5fquant_5fminiscope_5for s12 v40 v41 v12 v9 v30 v16 v2 ⦃ r s' => s'.Inv ∧ s12.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_4_eo__24is_5fquant_5fminiscope_5for
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s12
    req_same v40 v41 with h_v40 h_v41 using hinv12 hG
    req_stuck h_v40 as hq_v40 using hinv12 hG
    step as ⟨e_v42, he_v42⟩
    store_step with CtorSpec.eo_or.construct s12 e_v42 (by rw [he_v42]; exact empty_args) hinv12 h64 as ⟨v42, s13, hinv13, h_v42⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 dropping h_v40 h_v41 he_v42 hinv12 e_v42 s12 v40 v41
    store_step with Store.apply_rep s13 v42 v12 _ _ hinv13 h64 h_v42 h_v12 (by ns_tac) (by ns_tac) as ⟨v43, s14, hinv14, h_v43⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 h_v30 dropping h_v42 hinv13 s13 v42
    store_step with Store.apply_rep s14 v43 v9 _ _ hinv14 h64 h_v43 h_v9 (by ns_tac) (by ns_tac) as ⟨v44, s15, hinv15, h_v44⟩ growing hG carrying h_v2 h_v12 h_v16 h_v30 dropping h_v43 h_v9 hinv14 s14 v43 v9
    step as ⟨e_v45, he_v45⟩
    store_step with CtorSpec.eo_or.construct s15 e_v45 (by rw [he_v45]; exact empty_args) hinv15 h64 as ⟨v45, s16, hinv16, h_v45⟩ growing hG carrying h_v2 h_v12 h_v16 h_v30 h_v44 dropping he_v45 hinv15 e_v45 s15
    step as ⟨e_v46, he_v46⟩
    store_step with CtorSpec.eo_forall.construct s16 e_v46 (by rw [he_v46]; exact empty_args) hinv16 h64 as ⟨v46, s17, hinv17, h_v46⟩ growing hG carrying h_v2 h_v12 h_v16 h_v30 h_v44 h_v45 dropping he_v46 hinv16 e_v46 s16
    store_step with Store.apply_rep s17 v46 v30 _ _ hinv17 h64 h_v46 h_v30 (by ns_tac) (by ns_tac) as ⟨v47, s18, hinv18, h_v47⟩ growing hG carrying h_v2 h_v12 h_v16 h_v44 h_v45 dropping h_v30 h_v46 hinv17 s17 v30 v46
    store_step with Store.apply_rep s18 v47 v12 _ _ hinv18 h64 h_v47 h_v12 (by ns_tac) (by ns_tac) as ⟨v48, s19, hinv19, h_v48⟩ growing hG carrying h_v2 h_v16 h_v44 h_v45 dropping h_v12 h_v47 hinv18 s18 v12 v47
    store_step with Store.apply_rep s19 v45 v48 _ _ hinv19 h64 h_v45 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s20, hinv20, h_v49⟩ growing hG carrying h_v2 h_v16 h_v44 dropping h_v45 h_v48 hinv19 s19 v45 v48
    store_step with Store.apply_rep s20 v49 v16 _ _ hinv20 h64 h_v49 h_v16 (by ns_tac) (by ns_tac) as ⟨v50, s21, hinv21, h_v50⟩ growing hG carrying h_v2 h_v44 dropping h_v16 h_v49 hinv20 s20 v16 v49
    store_step with ih.eo__24is_5fquant_5fminiscope_5for s21 v2 v44 v50 _ _ _ hinv21 h64 (hG.rem hrem) h_v2 h_v44 h_v50 as ⟨v51, s22, hinv22, h_v51⟩ growing hG carrying dropping h_v2 h_v44 h_v50 hinv21 s21 v2 v44 v50
    req_done hinv22 hG with h_v51 using hq_v40)
  store_step with h_req_v52 as ⟨v52, s23, hinv23, h_v52⟩ growing hG carrying dropping h_req_v52 h_v12 h_v16 h_v2 h_v30 h_v40 h_v41 h_v9 hinv12 s12 v12 v16 v2 v30 v40 v41 v9
  case_done hinv23 hG with h_v52 in EoCases.__is_quant_miniscope_or.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19 hn_v22 hn_v23 hn_v25 hn_v26 hn_v29 hn_v30 hn_v32 hn_v33

theorem case_3_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_miniscope_or.case_3
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 hinv1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__is_quant_miniscope_or.case_3
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  pat_same a2 v2 with h_a2 h_v2 using hinv3 else hinv3 hG in EoCases.__is_quant_miniscope_or.case_3
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__is_quant_miniscope_or.case_3 using hn_a0 hn_a1 hn_a2

theorem case_4_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_4_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping
  case_done hinv1 hG with h_v0 in EoCases.__is_quant_miniscope_or.case_4 using hn_a0 hn_a1 hn_a2

theorem cases_0_0_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2 = none ∧ EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2 = none ∧ EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2 = none ∧ EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24is_5fquant_5fminiscope_5for_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] = [] ++ [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2
  group_step with case_1_eo__24is_5fquant_5fminiscope_5for_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] = [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hl_0
  group_step with case_2_eo__24is_5fquant_5fminiscope_5for_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] = [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1
  group_step with case_3_eo__24is_5fquant_5fminiscope_5for_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] = [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24is_5fquant_5fminiscope_5for_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] = [] ++ [EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2
  group_none hinv1 hG with hl_4

/-- logos's fall-through helpers of `__is_quant_miniscope_or`, each the program's cases from its first on. -/
theorem eo__24is_5fquant_5fminiscope_5for.helper_3 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_3___is_quant_miniscope_or x_a0 x_a1 x_a2 =
      firstSome [EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_3___is_quant_miniscope_or
  unfold EoCases.__is_quant_miniscope_or.case_3 EoCases.__is_quant_miniscope_or.case_4
  logos_eq_deep

theorem eo__24is_5fquant_5fminiscope_5for.helper_2 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_2___is_quant_miniscope_or x_a0 x_a1 x_a2 =
      firstSome [EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] HasStuck.stuck := by
  have hn := eo__24is_5fquant_5fminiscope_5for.helper_3
  conv => lhs; unfold Eo.__eo_l_2___is_quant_miniscope_or
  unfold EoCases.__is_quant_miniscope_or.case_2
  logos_eq_deep

theorem eo__24is_5fquant_5fminiscope_5for.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___is_quant_miniscope_or x_a0 x_a1 x_a2 =
      firstSome [EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] HasStuck.stuck := by
  have hn := eo__24is_5fquant_5fminiscope_5for.helper_2
  conv => lhs; unfold Eo.__eo_l_1___is_quant_miniscope_or
  unfold EoCases.__is_quant_miniscope_or.case_1
  logos_eq_deep

/-- logos's `__is_quant_miniscope_or` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fquant_5fminiscope_5for.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __is_quant_miniscope_or x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __is_quant_miniscope_or
  unfold EoCases.__is_quant_miniscope_or.case_0
  have hn := eo__24is_5fquant_5fminiscope_5for.helper_1
  logos_eq_deep

theorem body_eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24is_5fquant_5fminiscope_5for s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_quant_miniscope_or x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fquant_5fminiscope_5for.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24is_5fquant_5fminiscope_5for
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  body_group_step with cases_0_0_eo__24is_5fquant_5fminiscope_5for_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] = [] ++ [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2
  body_group_step with cases_0_1_eo__24is_5fquant_5fminiscope_5for_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] = [EoCases.__is_quant_miniscope_or.case_0 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_1 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_2 x_a0 x_a1 x_a2, EoCases.__is_quant_miniscope_or.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__is_quant_miniscope_or.case_4 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3 hl_4 in EoCases.__is_quant_miniscope_or.case_0 EoCases.__is_quant_miniscope_or.case_1 EoCases.__is_quant_miniscope_or.case_2 EoCases.__is_quant_miniscope_or.case_3 EoCases.__is_quant_miniscope_or.case_4

theorem eo__24is_5fquant_5fminiscope_5for_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fquant_5fminiscope_5for.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24is_5fquant_5fminiscope_5for
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 911#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24is_5fquant_5fminiscope_5for s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__is_quant_miniscope_or x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_911 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_911 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fquant_5fminiscope_5for_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5frenaming_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5frenaming_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_renaming_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__is_renaming_rec.case_0 x_a0 x_a1 = some (__is_renaming_rec y0 y1)
      | core.result.Result.Ok none => EoCases.__is_renaming_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5frenaming_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__is_renaming_rec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__is_renaming_rec.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__is_renaming_rec.case_0 using hn_a0 hn_a1

theorem case_1_eo__24is_5frenaming_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5frenaming_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_renaming_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__is_renaming_rec.case_1 x_a0 x_a1 = some (__is_renaming_rec y0 y1)
      | core.result.Result.Ok none => EoCases.__is_renaming_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5frenaming_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_renaming_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_renaming_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_renaming_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__is_renaming_rec.case_1
  obtain ⟨hn_v8, hn_v9⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv1 h_v5
  pat_unapply h_a1 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_renaming_rec.case_1
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__is_renaming_rec.case_1
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v16 (by rw [he_v16]; exact empty_args) hinv1 h64 as ⟨v16, s2, hinv2, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 h_v14 h_v15 dropping h_a1 h_v11 h_v4 h_v5 h_v6 h_v8 he_v16 hinv1 e_v16 s1 v11 v4 v5 v6 v8
  pat_same v14 v16 with h_v14 h_v16 using hinv2 else hinv2 hG in EoCases.__is_renaming_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v15 as ⟨v18, x_v18, h_v18⟩ ⟨v19, x_v19, h_v19⟩ else hinv2 hG in EoCases.__is_renaming_rec.case_1
  obtain ⟨hn_v18, hn_v19⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv2 h_v15
  pat_same v19 v9 with h_v19 h_v9 using hinv2 else hinv2 hG in EoCases.__is_renaming_rec.case_1
  case_again hinv2 hG with h_v2 h_v12 in EoCases.__is_renaming_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v14 hn_v15 hn_v18 hn_v19

/-- logos's `__is_renaming_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5frenaming_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __is_renaming_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_renaming_rec.case_0 x_a0 x_a1, EoCases.__is_renaming_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __is_renaming_rec
  unfold EoCases.__is_renaming_rec.case_0 EoCases.__is_renaming_rec.case_1
  logos_eq

theorem step_eo__24is_5frenaming_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24is_5frenaming_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__is_renaming_rec x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __is_renaming_rec x_a0 x_a1 = __is_renaming_rec y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5frenaming_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24is_5frenaming_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24is_5frenaming_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24is_5frenaming_5frec_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__is_renaming_rec.case_0 EoCases.__is_renaming_rec.case_1

theorem body_eo__24is_5frenaming_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24is_5frenaming_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_renaming_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24is_5frenaming_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_renaming_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24is_5frenaming_5frec body_eo__24is_5frenaming_5frec_loop
  step with step_eo__24is_5frenaming_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24is_5frenaming_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24is_5frenaming_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5frenaming_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24is_5frenaming_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 912#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24is_5frenaming_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__is_renaming_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_912 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_912 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5frenaming_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fseq_5fconst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fseq_5fconst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_seq_const.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_seq_const.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fseq_5fconst
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_seq_const.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__is_seq_const.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
  case_done hinv2 hG with h_v4 in EoCases.__is_seq_const.case_0 using hn_a0 hn_v1 hn_v2

theorem case_1_eo__24is_5fseq_5fconst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fseq_5fconst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_seq_const.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_seq_const.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fseq_5fconst
  have hG := Store.Grows.refl s
  store_step with ih.eo__24is_5fseq_5fconst_5frec s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping h_a0
  case_done hinv1 hG with h_v0 in EoCases.__is_seq_const.case_1 using hn_a0

/-- logos's `__is_seq_const` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fseq_5fconst.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __is_seq_const x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_seq_const.case_0 x_a0, EoCases.__is_seq_const.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __is_seq_const
  unfold EoCases.__is_seq_const.case_0 EoCases.__is_seq_const.case_1
  logos_eq

theorem body_eo__24is_5fseq_5fconst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24is_5fseq_5fconst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_seq_const x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fseq_5fconst.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24is_5fseq_5fconst
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24is_5fseq_5fconst_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24is_5fseq_5fconst_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__is_seq_const.case_0 EoCases.__is_seq_const.case_1

theorem eo__24is_5fseq_5fconst_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fseq_5fconst.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24is_5fseq_5fconst
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24is_5fseq_5fconst s1 a0) (fun s' t => Represents.rep s' t (__is_seq_const x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fseq_5fconst_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5fseq_5fconst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_seq_const_rec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__is_seq_const_rec.case_0 x_a0 = some (__is_seq_const_rec y0)
      | core.result.Result.Ok none => EoCases.__is_seq_const_rec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fseq_5fconst_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_seq_const_rec.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_seq_const_rec.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_seq_const_rec.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_seq_const_rec.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v8 dropping h_v4 h_v5 h_v6 h_v9 he_v10 hinv1 e_v10 s1 v4 v5 v6 v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__is_seq_const_rec.case_0
  case_again hinv2 hG with h_v2 in EoCases.__is_seq_const_rec.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

theorem case_1_eo__24is_5fseq_5fconst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_seq_const_rec.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__is_seq_const_rec.case_1 x_a0 = some (__is_seq_const_rec y0)
      | core.result.Result.Ok none => EoCases.__is_seq_const_rec.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fseq_5fconst_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_seq_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__is_seq_const_rec.case_1
  obtain hn_v1 := CtorSpec.eo_seq_2eempty.fields_ne_stuck hinv h_a0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__is_seq_const_rec.case_1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_Seq.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 dropping h_a0 h_v1 h_v4 he_v5 e_v5 v1 v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__is_seq_const_rec.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying dropping h_v3 h_v5 hinv1 s1 v3 v5
  case_done hinv2 hG with h_v6 in EoCases.__is_seq_const_rec.case_1 using hn_a0 hn_v1 hn_v3 hn_v4

theorem case_2_eo__24is_5fseq_5fconst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__is_seq_const_rec.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__is_seq_const_rec.case_2 x_a0 = some (__is_seq_const_rec y0)
      | core.result.Result.Ok none => EoCases.__is_seq_const_rec.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24is_5fseq_5fconst_5frec
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping
  case_done hinv1 hG with h_v0 in EoCases.__is_seq_const_rec.case_2 using hn_a0

/-- logos's `__is_seq_const_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fseq_5fconst_5frec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __is_seq_const_rec x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_seq_const_rec.case_0 x_a0, EoCases.__is_seq_const_rec.case_1 x_a0, EoCases.__is_seq_const_rec.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __is_seq_const_rec
  unfold EoCases.__is_seq_const_rec.case_0 EoCases.__is_seq_const_rec.case_1 EoCases.__is_seq_const_rec.case_2
  logos_eq

theorem step_eo__24is_5fseq_5fconst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__is_seq_const_rec x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __is_seq_const_rec x_a0 = __is_seq_const_rec y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fseq_5fconst_5frec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24is_5fseq_5fconst_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  round_step with case_0_eo__24is_5fseq_5fconst_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using hn_a0
  round_step with case_1_eo__24is_5fseq_5fconst_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hn_a0 hc0
  round_step with case_2_eo__24is_5fseq_5fconst_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hn_a0 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hc0 hc1 hc2 in EoCases.__is_seq_const_rec.case_0 EoCases.__is_seq_const_rec.case_1 EoCases.__is_seq_const_rec.case_2

theorem body_eo__24is_5fseq_5fconst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_seq_const_rec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24is_5fseq_5fconst_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_seq_const_rec x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24is_5fseq_5fconst_5frec body_eo__24is_5fseq_5fconst_5frec_loop
  step with step_eo__24is_5fseq_5fconst_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24is_5fseq_5fconst_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24is_5fseq_5fconst_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fseq_5fconst_5frec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24is_5fseq_5fconst_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 914#u32 _ [a0] rfl
    (fun s1 => body_eo__24is_5fseq_5fconst_5frec s1 a0) (fun s' t => Represents.rep s' t (__is_seq_const_rec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_914 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_914 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fseq_5fconst_5frec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24least_5fint_5fgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24least_5fint_5fgt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__least_int_gt.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__least_int_gt.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24least_5fint_5fgt
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 1#u32 (1) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_to_z s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_v0 dropping h_a0 he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_add s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_v0 h_v1 he_v2 hinv2 e_v2 s2 v0 v1
  case_done hinv3 hG with h_v2 in EoCases.__least_int_gt.case_0 using hn_a0

/-- logos's `__least_int_gt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24least_5fint_5fgt.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __least_int_gt x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__least_int_gt.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __least_int_gt
  unfold EoCases.__least_int_gt.case_0
  logos_eq

theorem body_eo__24least_5fint_5fgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24least_5fint_5fgt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__least_int_gt x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24least_5fint_5fgt.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24least_5fint_5fgt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24least_5fint_5fgt_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__least_int_gt.case_0

theorem eo__24least_5fint_5fgt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24least_5fint_5fgt.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24least_5fint_5fgt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24least_5fint_5fgt s1 a0) (fun s' t => Represents.rep s' t (__least_int_gt x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24least_5fint_5fgt_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24lower_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24lower_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__lower_not_and.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__lower_not_and.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24lower_5fnot_5fand
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__lower_not_and.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__lower_not_and.case_0 using hn_a0

theorem case_1_eo__24lower_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24lower_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__lower_not_and.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__lower_not_and.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24lower_5fnot_5fand
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__lower_not_and.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__lower_not_and.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__lower_not_and.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v7 dropping h_v5 h_v8 hinv3 s3 v5 v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 dropping h_v7 h_v9 hinv4 s4 v7 v9
  store_step with ih.eo__24lower_5fnot_5fand s5 v2 _ hinv5 h64 (hG.rem hrem) h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v10 dropping h_v2 hinv5 s5 v2
  store_step with Store.apply_mk_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying dropping h_v10 h_v11 hinv6 s6 v10 v11
  case_done hinv7 hG with h_v12 in EoCases.__lower_not_and.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__lower_not_and` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24lower_5fnot_5fand.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __lower_not_and x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__lower_not_and.case_0 x_a0, EoCases.__lower_not_and.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __lower_not_and
  unfold EoCases.__lower_not_and.case_0 EoCases.__lower_not_and.case_1
  logos_eq

theorem body_eo__24lower_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24lower_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__lower_not_and x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24lower_5fnot_5fand.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24lower_5fnot_5fand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24lower_5fnot_5fand_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24lower_5fnot_5fand_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__lower_not_and.case_0 EoCases.__lower_not_and.case_1

theorem eo__24lower_5fnot_5fand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24lower_5fnot_5fand.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24lower_5fnot_5fand
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 917#u32 _ [a0] rfl
    (fun s1 => body_eo__24lower_5fnot_5fand s1 a0) (fun s' t => Represents.rep s' t (__lower_not_and x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_917 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_917 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24lower_5fnot_5fand_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5farith_5fmult_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5farith_5fmult_5fneg s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_neg.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_neg.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5farith_5fmult_5fneg
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_neg.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_neg.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2a.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  store_step with Store.apply_rep s1 v6 a0 _ _ hinv1 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_v6 hinv1 s1 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v4 h_v7 dropping h_v5 h_v8 hinv3 s3 v5 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v2 h_v4 h_v7 h_v9 dropping he_v10 hinv4 e_v10 s4
  store_step with ih.eo__24eo_5ftypeof s5 a0 _ hinv5 h64 (hG.rem hrem) h_a0 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v2 h_v4 h_v7 h_v9 h_v10 dropping hinv5 s5
  store_step with ih.eo__24eo_5fnil s6 v10 v11 _ _ hinv6 h64 (hG.rem hrem) h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v2 h_v4 h_v7 h_v9 dropping h_v10 h_v11 hinv6 s6 v10 v11
  store_step with Store.apply_mk_rep s7 v9 v12 _ _ hinv7 h64 h_v9 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v2 h_v4 h_v7 dropping h_v12 h_v9 hinv7 s7 v12 v9
  store_step with Store.apply_mk_rep s8 v7 v13 _ _ hinv8 h64 h_v7 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v2 h_v4 dropping h_v13 h_v7 hinv8 s8 v13 v7
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2a.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v2 h_v4 h_v14 dropping he_v15 hinv9 e_v15 s9
  store_step with Store.apply_rep s10 v15 a0 _ _ hinv10 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v2 h_v4 h_v14 dropping h_v15 hinv10 s10 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__2a.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v2 h_v4 h_v14 h_v16 dropping he_v17 hinv11 e_v17 s11
  store_step with Store.apply_rep s12 v17 v2 _ _ hinv12 h64 h_v17 h_v2 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v4 h_v14 h_v16 dropping h_v17 h_v2 hinv12 s12 v17 v2
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__2a.construct s13 e_v19 (by rw [he_v19]; exact empty_args) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v4 h_v14 h_v16 h_v18 dropping he_v19 hinv13 e_v19 s13
  store_step with ih.eo__24eo_5ftypeof s14 a0 _ hinv14 h64 (hG.rem hrem) h_a0 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v4 h_v14 h_v16 h_v18 h_v19 dropping h_a0 hinv14 s14
  store_step with ih.eo__24eo_5fnil s15 v19 v20 _ _ hinv15 h64 (hG.rem hrem) h_v19 h_v20 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v4 h_v14 h_v16 h_v18 dropping h_v19 h_v20 hinv15 s15 v19 v20
  store_step with Store.apply_mk_rep s16 v18 v21 _ _ hinv16 h64 h_v18 h_v21 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v4 h_v14 h_v16 dropping h_v18 h_v21 hinv16 s16 v18 v21
  store_step with Store.apply_mk_rep s17 v16 v22 _ _ hinv17 h64 h_v16 h_v22 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v4 h_v14 dropping h_v16 h_v22 hinv17 s17 v16 v22
  store_step with ih.eo__24arith_5frel_5finv s18 v4 v14 v23 _ _ _ hinv18 h64 (hG.rem hrem) h_v4 h_v14 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying dropping h_v14 h_v23 h_v4 hinv18 s18 v14 v23 v4
  case_done hinv19 hG with h_v24 in EoCases.__mk_arith_mult_neg.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__mk_arith_mult_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5farith_5fmult_5fneg.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_arith_mult_neg x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_arith_mult_neg.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_arith_mult_neg
  unfold EoCases.__mk_arith_mult_neg.case_0
  logos_eq

theorem body_eo__24mk_5farith_5fmult_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5farith_5fmult_5fneg s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_mult_neg x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5farith_5fmult_5fneg.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5farith_5fmult_5fneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5farith_5fmult_5fneg_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__mk_arith_mult_neg.case_0

theorem eo__24mk_5farith_5fmult_5fneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5farith_5fmult_5fneg.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5farith_5fmult_5fneg
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5farith_5fmult_5fneg s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_arith_mult_neg x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5farith_5fmult_5fneg_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_pos.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 h_v9 dropping he_v10 hinv4 e_v10 s4
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v10 h_v5 hinv5 s5 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__2a.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping he_v12 hinv6 e_v12 s6
  store_step with ih.eo__24eo_5ftypeof s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 h_v12 dropping hinv7 s7
  store_step with ih.eo__24eo_5fnil s8 v12 v13 _ _ hinv8 h64 (hG.rem hrem) h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping h_v12 h_v13 hinv8 s8 v12 v13
  store_step with Store.apply_mk_rep s9 v11 v14 _ _ hinv9 h64 h_v11 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v11 h_v14 hinv9 s9 v11 v14
  store_step with Store.apply_mk_rep s10 v9 v15 _ _ hinv10 h64 h_v9 h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v2 h_v7 dropping h_v15 h_v9 hinv10 s10 v15 v9
  store_step with Store.apply_mk_rep s11 v7 v16 _ _ hinv11 h64 h_v7 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v2 dropping h_v16 h_v7 hinv11 s11 v16 v7
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__2a.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v2 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 a0 _ _ hinv13 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v2 h_v17 dropping h_v18 hinv13 s13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_v2 h_v17 h_v19 dropping he_v20 hinv14 e_v20 s14
  store_step with Store.apply_rep s15 v20 v2 _ _ hinv15 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_v17 h_v19 dropping h_v2 h_v20 hinv15 s15 v2 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2a.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_v17 h_v19 h_v21 dropping he_v22 hinv16 e_v22 s16
  store_step with ih.eo__24eo_5ftypeof s17 a0 _ hinv17 h64 (hG.rem hrem) h_a0 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v17 h_v19 h_v21 h_v22 dropping h_a0 hinv17 s17
  store_step with ih.eo__24eo_5fnil s18 v22 v23 _ _ hinv18 h64 (hG.rem hrem) h_v22 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v17 h_v19 h_v21 dropping h_v22 h_v23 hinv18 s18 v22 v23
  store_step with Store.apply_mk_rep s19 v21 v24 _ _ hinv19 h64 h_v21 h_v24 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v24 hinv19 s19 v21 v24
  store_step with Store.apply_mk_rep s20 v19 v25 _ _ hinv20 h64 h_v19 h_v25 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v17 dropping h_v19 h_v25 hinv20 s20 v19 v25
  store_step with Store.apply_mk_rep s21 v17 v26 _ _ hinv21 h64 h_v17 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v17 h_v26 hinv21 s21 v17 v26
  case_done hinv22 hG with h_v27 in EoCases.__mk_arith_mult_pos.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_pos.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 h_v9 dropping he_v10 hinv4 e_v10 s4
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v10 h_v5 hinv5 s5 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__2a.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping he_v12 hinv6 e_v12 s6
  store_step with ih.eo__24eo_5ftypeof s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 h_v12 dropping hinv7 s7
  store_step with ih.eo__24eo_5fnil s8 v12 v13 _ _ hinv8 h64 (hG.rem hrem) h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping h_v12 h_v13 hinv8 s8 v12 v13
  store_step with Store.apply_mk_rep s9 v11 v14 _ _ hinv9 h64 h_v11 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v11 h_v14 hinv9 s9 v11 v14
  store_step with Store.apply_mk_rep s10 v9 v15 _ _ hinv10 h64 h_v9 h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v2 h_v7 dropping h_v15 h_v9 hinv10 s10 v15 v9
  store_step with Store.apply_mk_rep s11 v7 v16 _ _ hinv11 h64 h_v7 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v2 dropping h_v16 h_v7 hinv11 s11 v16 v7
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__2a.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v2 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 a0 _ _ hinv13 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v2 h_v17 dropping h_v18 hinv13 s13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_v2 h_v17 h_v19 dropping he_v20 hinv14 e_v20 s14
  store_step with Store.apply_rep s15 v20 v2 _ _ hinv15 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_v17 h_v19 dropping h_v2 h_v20 hinv15 s15 v2 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2a.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_v17 h_v19 h_v21 dropping he_v22 hinv16 e_v22 s16
  store_step with ih.eo__24eo_5ftypeof s17 a0 _ hinv17 h64 (hG.rem hrem) h_a0 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v17 h_v19 h_v21 h_v22 dropping h_a0 hinv17 s17
  store_step with ih.eo__24eo_5fnil s18 v22 v23 _ _ hinv18 h64 (hG.rem hrem) h_v22 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v17 h_v19 h_v21 dropping h_v22 h_v23 hinv18 s18 v22 v23
  store_step with Store.apply_mk_rep s19 v21 v24 _ _ hinv19 h64 h_v21 h_v24 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v24 hinv19 s19 v21 v24
  store_step with Store.apply_mk_rep s20 v19 v25 _ _ hinv20 h64 h_v19 h_v25 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v17 dropping h_v19 h_v25 hinv20 s20 v19 v25
  store_step with Store.apply_mk_rep s21 v17 v26 _ _ hinv21 h64 h_v17 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v17 h_v26 hinv21 s21 v17 v26
  case_done hinv22 hG with h_v27 in EoCases.__mk_arith_mult_pos.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_pos.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 h_v9 dropping he_v10 hinv4 e_v10 s4
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v10 h_v5 hinv5 s5 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__2a.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping he_v12 hinv6 e_v12 s6
  store_step with ih.eo__24eo_5ftypeof s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 h_v12 dropping hinv7 s7
  store_step with ih.eo__24eo_5fnil s8 v12 v13 _ _ hinv8 h64 (hG.rem hrem) h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping h_v12 h_v13 hinv8 s8 v12 v13
  store_step with Store.apply_mk_rep s9 v11 v14 _ _ hinv9 h64 h_v11 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v11 h_v14 hinv9 s9 v11 v14
  store_step with Store.apply_mk_rep s10 v9 v15 _ _ hinv10 h64 h_v9 h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v2 h_v7 dropping h_v15 h_v9 hinv10 s10 v15 v9
  store_step with Store.apply_mk_rep s11 v7 v16 _ _ hinv11 h64 h_v7 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v2 dropping h_v16 h_v7 hinv11 s11 v16 v7
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__2a.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v2 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 a0 _ _ hinv13 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v2 h_v17 dropping h_v18 hinv13 s13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_v2 h_v17 h_v19 dropping he_v20 hinv14 e_v20 s14
  store_step with Store.apply_rep s15 v20 v2 _ _ hinv15 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_v17 h_v19 dropping h_v2 h_v20 hinv15 s15 v2 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2a.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_v17 h_v19 h_v21 dropping he_v22 hinv16 e_v22 s16
  store_step with ih.eo__24eo_5ftypeof s17 a0 _ hinv17 h64 (hG.rem hrem) h_a0 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v17 h_v19 h_v21 h_v22 dropping h_a0 hinv17 s17
  store_step with ih.eo__24eo_5fnil s18 v22 v23 _ _ hinv18 h64 (hG.rem hrem) h_v22 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v17 h_v19 h_v21 dropping h_v22 h_v23 hinv18 s18 v22 v23
  store_step with Store.apply_mk_rep s19 v21 v24 _ _ hinv19 h64 h_v21 h_v24 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v24 hinv19 s19 v21 v24
  store_step with Store.apply_mk_rep s20 v19 v25 _ _ hinv20 h64 h_v19 h_v25 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v17 dropping h_v19 h_v25 hinv20 s20 v19 v25
  store_step with Store.apply_mk_rep s21 v17 v26 _ _ hinv21 h64 h_v17 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v17 h_v26 hinv21 s21 v17 v26
  case_done hinv22 hG with h_v27 in EoCases.__mk_arith_mult_pos.case_2 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_3_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_3_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_3
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_3
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_pos.case_3
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 h_v9 dropping he_v10 hinv4 e_v10 s4
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v10 h_v5 hinv5 s5 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__2a.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping he_v12 hinv6 e_v12 s6
  store_step with ih.eo__24eo_5ftypeof s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 h_v12 dropping hinv7 s7
  store_step with ih.eo__24eo_5fnil s8 v12 v13 _ _ hinv8 h64 (hG.rem hrem) h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping h_v12 h_v13 hinv8 s8 v12 v13
  store_step with Store.apply_mk_rep s9 v11 v14 _ _ hinv9 h64 h_v11 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v11 h_v14 hinv9 s9 v11 v14
  store_step with Store.apply_mk_rep s10 v9 v15 _ _ hinv10 h64 h_v9 h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v2 h_v7 dropping h_v15 h_v9 hinv10 s10 v15 v9
  store_step with Store.apply_mk_rep s11 v7 v16 _ _ hinv11 h64 h_v7 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v2 dropping h_v16 h_v7 hinv11 s11 v16 v7
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__2a.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v2 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 a0 _ _ hinv13 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v2 h_v17 dropping h_v18 hinv13 s13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_v2 h_v17 h_v19 dropping he_v20 hinv14 e_v20 s14
  store_step with Store.apply_rep s15 v20 v2 _ _ hinv15 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_v17 h_v19 dropping h_v2 h_v20 hinv15 s15 v2 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2a.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_v17 h_v19 h_v21 dropping he_v22 hinv16 e_v22 s16
  store_step with ih.eo__24eo_5ftypeof s17 a0 _ hinv17 h64 (hG.rem hrem) h_a0 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v17 h_v19 h_v21 h_v22 dropping h_a0 hinv17 s17
  store_step with ih.eo__24eo_5fnil s18 v22 v23 _ _ hinv18 h64 (hG.rem hrem) h_v22 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v17 h_v19 h_v21 dropping h_v22 h_v23 hinv18 s18 v22 v23
  store_step with Store.apply_mk_rep s19 v21 v24 _ _ hinv19 h64 h_v21 h_v24 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v24 hinv19 s19 v21 v24
  store_step with Store.apply_mk_rep s20 v19 v25 _ _ hinv20 h64 h_v19 h_v25 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v17 dropping h_v19 h_v25 hinv20 s20 v19 v25
  store_step with Store.apply_mk_rep s21 v17 v26 _ _ hinv21 h64 h_v17 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v17 h_v26 hinv21 s21 v17 v26
  case_done hinv22 hG with h_v27 in EoCases.__mk_arith_mult_pos.case_3 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_4_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_4_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_4
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_pos.case_4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_pos.case_4
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v2 h_v5 h_v7 h_v9 dropping he_v10 hinv4 e_v10 s4
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v10 h_v5 hinv5 s5 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__2a.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping he_v12 hinv6 e_v12 s6
  store_step with ih.eo__24eo_5ftypeof s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 h_v12 dropping hinv7 s7
  store_step with ih.eo__24eo_5fnil s8 v12 v13 _ _ hinv8 h64 (hG.rem hrem) h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 h_v11 dropping h_v12 h_v13 hinv8 s8 v12 v13
  store_step with Store.apply_mk_rep s9 v11 v14 _ _ hinv9 h64 h_v11 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_v2 h_v7 h_v9 dropping h_v11 h_v14 hinv9 s9 v11 v14
  store_step with Store.apply_mk_rep s10 v9 v15 _ _ hinv10 h64 h_v9 h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_v2 h_v7 dropping h_v15 h_v9 hinv10 s10 v15 v9
  store_step with Store.apply_mk_rep s11 v7 v16 _ _ hinv11 h64 h_v7 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_v2 dropping h_v16 h_v7 hinv11 s11 v16 v7
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__2a.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_v2 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 a0 _ _ hinv13 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_v2 h_v17 dropping h_v18 hinv13 s13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_v2 h_v17 h_v19 dropping he_v20 hinv14 e_v20 s14
  store_step with Store.apply_rep s15 v20 v2 _ _ hinv15 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_v17 h_v19 dropping h_v2 h_v20 hinv15 s15 v2 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2a.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_v17 h_v19 h_v21 dropping he_v22 hinv16 e_v22 s16
  store_step with ih.eo__24eo_5ftypeof s17 a0 _ hinv17 h64 (hG.rem hrem) h_a0 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v17 h_v19 h_v21 h_v22 dropping h_a0 hinv17 s17
  store_step with ih.eo__24eo_5fnil s18 v22 v23 _ _ hinv18 h64 (hG.rem hrem) h_v22 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v17 h_v19 h_v21 dropping h_v22 h_v23 hinv18 s18 v22 v23
  store_step with Store.apply_mk_rep s19 v21 v24 _ _ hinv19 h64 h_v21 h_v24 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v24 hinv19 s19 v21 v24
  store_step with Store.apply_mk_rep s20 v19 v25 _ _ hinv20 h64 h_v19 h_v25 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v17 dropping h_v19 h_v25 hinv20 s20 v19 v25
  store_step with Store.apply_mk_rep s21 v17 v26 _ _ hinv21 h64 h_v17 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v17 h_v26 hinv21 s21 v17 v26
  case_done hinv22 hG with h_v27 in EoCases.__mk_arith_mult_pos.case_4 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem cases_0_0_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1 = none ∧ EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1 = none ∧ EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1 = none ∧ EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24mk_5farith_5fmult_5fpos_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] = [] ++ [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1
  group_step with case_1_eo__24mk_5farith_5fmult_5fpos_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] = [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hl_0
  group_step with case_2_eo__24mk_5farith_5fmult_5fpos_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] = [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hl_0 hl_1
  group_step with case_3_eo__24mk_5farith_5fmult_5fpos_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] = [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24mk_5farith_5fmult_5fpos_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] = [] ++ [EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1
  group_none hinv1 hG with hl_4

/-- logos's `__mk_arith_mult_pos` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5farith_5fmult_5fpos.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_arith_mult_pos x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_arith_mult_pos
  unfold EoCases.__mk_arith_mult_pos.case_0 EoCases.__mk_arith_mult_pos.case_1 EoCases.__mk_arith_mult_pos.case_2 EoCases.__mk_arith_mult_pos.case_3 EoCases.__mk_arith_mult_pos.case_4
  logos_eq

theorem body_eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5farith_5fmult_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_mult_pos x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5farith_5fmult_5fpos.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5farith_5fmult_5fpos
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  body_group_step with cases_0_0_eo__24mk_5farith_5fmult_5fpos_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] = [] ++ [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1
  body_group_step with cases_0_1_eo__24mk_5farith_5fmult_5fpos_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] = [EoCases.__mk_arith_mult_pos.case_0 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_1 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_2 x_a0 x_a1, EoCases.__mk_arith_mult_pos.case_3 x_a0 x_a1] ++ [EoCases.__mk_arith_mult_pos.case_4 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 in EoCases.__mk_arith_mult_pos.case_0 EoCases.__mk_arith_mult_pos.case_1 EoCases.__mk_arith_mult_pos.case_2 EoCases.__mk_arith_mult_pos.case_3 EoCases.__mk_arith_mult_pos.case_4

theorem eo__24mk_5farith_5fmult_5fpos_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5farith_5fmult_5fpos.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5farith_5fmult_5fpos
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5farith_5fmult_5fpos s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_arith_mult_pos x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5farith_5fmult_5fpos_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5farith_5fmult_5fsign_5fsgn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_sign_sgn.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_sign_sgn.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5farith_5fmult_5fsign_5fsgn
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 dropping h_v4 h_v5 h_v6 he_v10 hinv1 e_v10 s1 v4 v5 v6
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v17 (by rw [he_v17]; exact empty_args) hinv2 h64 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_a0 h_a2 h_v2 h_v13 h_v15 h_v16 dropping h_v10 h_v12 h_v8 h_v9 he_v17 hinv2 e_v17 s2 v10 v12 v8 v9
  pat_same v15 v17 with h_v15 h_v17 using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_a2 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v19 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__2a.construct s3 e_v24 (by rw [he_v24]; exact empty_args) hinv3 h64 as ⟨v24, s4, hinv4, h_v24⟩ growing hG carrying h_a0 h_v2 h_v13 h_v16 h_v20 h_v22 h_v23 dropping h_a2 h_v15 h_v17 h_v19 he_v24 hinv3 e_v24 s3 v15 v17 v19
  pat_same v22 v24 with h_v22 h_v24 using hinv4 else hinv4 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_same v23 v16 with h_v23 h_v16 using hinv4 else hinv4 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v20 as ⟨v26, v27, x_v26, x_v27, h_v26, h_v27, hn_v26, hn_v27⟩ using hinv4 else hinv4 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_unapply h_v26 as ⟨v29, v30, x_v29, x_v30, h_v29, h_v30, hn_v29, hn_v30⟩ using hinv4 else hinv4 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo__2a.construct s4 e_v31 (by rw [he_v31]; exact empty_args) hinv4 h64 as ⟨v31, s5, hinv5, h_v31⟩ growing hG carrying h_a0 h_v2 h_v13 h_v16 h_v27 h_v29 h_v30 dropping h_v20 h_v22 h_v23 h_v24 h_v26 he_v31 hinv4 e_v31 s4 v20 v22 v23 v24 v26
  pat_same v29 v31 with h_v29 h_v31 using hinv5 else hinv5 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  pat_same v30 v16 with h_v30 h_v16 using hinv5 else hinv5 hG in EoCases.__mk_arith_mult_sign_sgn.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with Store.builtin_spec_to_q s5 e_v32 (by rw [he_v32]; rfl) h_v13 hinv5 h64 as ⟨v32, s6, hinv6, h_v32⟩ growing hG carrying h_a0 h_v2 h_v16 h_v27 dropping h_v13 h_v29 h_v30 h_v31 he_v32 hinv5 e_v32 s5 v13 v29 v30 v31
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s6 _ hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_v2 h_v16 h_v27 h_v32 dropping hinv6 s6
  replace h_v34 := Represents.rep_of_eq h_v34 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  have h_req_v37 := (show requires_0_eo__24mk_5farith_5fmult_5fsign_5fsgn s7 v32 v34 v16 v27 a0 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24mk_5farith_5fmult_5fsign_5fsgn
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v32 v34 with h_v32 h_v34 using hinv7 hG
    req_stuck h_v32 as hq_v32 using hinv7 hG
    store_step with ih.eo__24strip_5feven_5fexponent s7 v16 v27 _ _ hinv7 h64 (hG.rem hrem) h_v16 h_v27 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_v2 dropping h_v16 h_v27 h_v32 h_v34 hinv7 s7 v16 v27 v32 v34
    store_step with ih.eo__24mk_5farith_5fmult_5fsign_5fsgn s8 a0 v2 v35 _ _ _ hinv8 h64 (hG.rem hrem) h_a0 h_v2 h_v35 as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying dropping h_a0 h_v2 h_v35 hinv8 s8 v2 v35
    req_done hinv9 hG with h_v36 using hq_v32)
  store_step with h_req_v37 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying dropping h_req_v37 h_v16 h_v2 h_v27 h_v32 h_v34 hinv7 s7 v16 v2 v27 v32 v34
  case_done hinv10 hG with h_v37 in EoCases.__mk_arith_mult_sign_sgn.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v12 hn_v13 hn_v15 hn_v16 hn_v19 hn_v20 hn_v22 hn_v23 hn_v26 hn_v27 hn_v29 hn_v30

theorem case_1_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5farith_5fmult_5fsign_5fsgn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_sign_sgn.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_sign_sgn.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5farith_5fmult_5fsign_5fsgn
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a2 h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  pat_unapply h_a2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_v2 h_v9 h_v12 h_v16 h_v18 h_v19 dropping h_a2 h_v11 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  pat_same v19 v12 with h_v19 h_v12 using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_1
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_to_q s3 e_v21 (by rw [he_v21]; rfl) h_v9 hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_v2 h_v12 h_v16 dropping h_v18 h_v19 h_v20 h_v9 he_v21 hinv3 e_v21 s3 v18 v19 v20 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s4 _ hinv4 h64 as ⟨v23, s5, hinv5, h_v23⟩ growing hG carrying h_a0 h_v2 h_v12 h_v16 h_v21 dropping hinv4 s4
  replace h_v23 := Represents.rep_of_eq h_v23 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  have h_req_v26 := (show requires_2_eo__24mk_5farith_5fmult_5fsign_5fsgn s5 v21 v23 v12 v16 a0 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_2_eo__24mk_5farith_5fmult_5fsign_5fsgn
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v21 v23 with h_v21 h_v23 using hinv5 hG
    req_stuck h_v21 as hq_v21 using hinv5 hG
    store_step with ih.eo__24strip_5feven_5fexponent s5 v12 v16 _ _ hinv5 h64 (hG.rem hrem) h_v12 h_v16 as ⟨v24, s6, hinv6, h_v24⟩ growing hG carrying h_a0 h_v2 dropping h_v12 h_v16 h_v21 h_v23 hinv5 s5 v12 v16 v21 v23
    store_step with ih.eo__24mk_5farith_5fmult_5fsign_5fsgn s6 a0 v2 v24 _ _ _ hinv6 h64 (hG.rem hrem) h_a0 h_v2 h_v24 as ⟨v25, s7, hinv7, h_v25⟩ growing hG carrying dropping h_a0 h_v2 h_v24 hinv6 s6 v2 v24
    req_done hinv7 hG with h_v25 using hq_v21)
  store_step with h_req_v26 as ⟨v26, s8, hinv8, h_v26⟩ growing hG carrying dropping h_req_v26 h_v12 h_v16 h_v2 h_v21 h_v23 hinv5 s5 v12 v16 v2 v21 v23
  case_done hinv8 hG with h_v26 in EoCases.__mk_arith_mult_sign_sgn.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

theorem case_2_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24mk_5farith_5fmult_5fsign_5fsgn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_sign_sgn.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_sign_sgn.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24mk_5farith_5fmult_5fsign_5fsgn
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a2 h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  pat_unapply h_a2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__2a.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_v2 h_v9 h_v12 h_v16 h_v18 h_v19 dropping h_a2 h_v11 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  pat_same v19 v12 with h_v19 h_v12 using hinv3 else hinv3 hG in EoCases.__mk_arith_mult_sign_sgn.case_2
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_to_q s3 e_v21 (by rw [he_v21]; rfl) h_v9 hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_v2 h_v12 h_v16 dropping h_v18 h_v19 h_v20 h_v9 he_v21 hinv3 e_v21 s3 v18 v19 v20 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s4 _ hinv4 h64 as ⟨v23, s5, hinv5, h_v23⟩ growing hG carrying h_a0 h_v2 h_v12 h_v16 h_v21 dropping hinv4 s4
  replace h_v23 := Represents.rep_of_eq h_v23 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  have h_req_v27 := (show requires_4_eo__24mk_5farith_5fmult_5fsign_5fsgn s5 v21 v23 a0 v12 v16 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_4_eo__24mk_5farith_5fmult_5fsign_5fsgn
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v21 v23 with h_v21 h_v23 using hinv5 hG
    req_stuck h_v21 as hq_v21 using hinv5 hG
    step as ⟨e_v24, he_v24⟩
    store_step with Store.builtin_spec_not s5 e_v24 (by rw [he_v24]; rfl) h_a0 hinv5 h64 as ⟨v24, s6, hinv6, h_v24⟩ growing hG carrying h_v2 h_v12 h_v16 dropping h_a0 h_v21 h_v23 he_v24 hinv5 e_v24 s5 v21 v23
    store_step with ih.eo__24strip_5feven_5fexponent s6 v12 v16 _ _ hinv6 h64 (hG.rem hrem) h_v12 h_v16 as ⟨v25, s7, hinv7, h_v25⟩ growing hG carrying h_v2 h_v24 dropping h_v12 h_v16 hinv6 s6 v12 v16
    store_step with ih.eo__24mk_5farith_5fmult_5fsign_5fsgn s7 v24 v2 v25 _ _ _ hinv7 h64 (hG.rem hrem) h_v24 h_v2 h_v25 as ⟨v26, s8, hinv8, h_v26⟩ growing hG carrying dropping h_v2 h_v24 h_v25 hinv7 s7 v2 v24 v25
    req_done hinv8 hG with h_v26 using hq_v21)
  store_step with h_req_v27 as ⟨v27, s9, hinv9, h_v27⟩ growing hG carrying dropping h_req_v27 h_v12 h_v16 h_v2 h_v21 h_v23 hinv5 s5 v12 v16 v2 v21 v23
  case_done hinv9 hG with h_v27 in EoCases.__mk_arith_mult_sign_sgn.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

theorem case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_mult_sign_sgn.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_mult_sign_sgn.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_arith_mult_sign_sgn.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_to_q s1 e_v1 (by rw [he_v1]; rfl) h_a2 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 dropping h_a1 h_a2 h_v0 he_v1 hinv1 e_v1 s1 v0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s2 _ hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 dropping hinv2 s2
  replace h_v3 := Represents.rep_of_eq h_v3 (y := Eo.Term.Rational (SmtEval.native_mk_rational (1) (1))) (by simp [SmtEval.native_mk_rational])
  have h_req_v4 := (show requires_6_eo__24mk_5farith_5fmult_5fsign_5fsgn s3 v1 v3 a0 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_6_eo__24mk_5farith_5fmult_5fsign_5fsgn
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v1 v3 with h_v1 h_v3 using hinv3 hG
    req_stuck h_v1 as hq_v1 using hinv3 hG
    req_done hinv3 hG with h_a0 using hq_v1)
  store_step with h_req_v4 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying dropping h_req_v4 h_v1 h_v3 hinv3 s3 v1 v3
  case_done hinv4 hG with h_v4 in EoCases.__mk_arith_mult_sign_sgn.case_3 using hn_a0 hn_a1 hn_a2

/-- logos's fall-through helpers of `__mk_arith_mult_sign_sgn`, each the program's cases from its first on. -/
theorem eo__24mk_5farith_5fmult_5fsign_5fsgn.helper_3 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_3___mk_arith_mult_sign_sgn x_a0 x_a1 x_a2 =
      firstSome [EoCases.__mk_arith_mult_sign_sgn.case_3 x_a0 x_a1 x_a2] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_3___mk_arith_mult_sign_sgn
  unfold EoCases.__mk_arith_mult_sign_sgn.case_3
  logos_eq_deep

theorem eo__24mk_5farith_5fmult_5fsign_5fsgn.helper_2 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_2___mk_arith_mult_sign_sgn x_a0 x_a1 x_a2 =
      firstSome [EoCases.__mk_arith_mult_sign_sgn.case_2 x_a0 x_a1 x_a2, EoCases.__mk_arith_mult_sign_sgn.case_3 x_a0 x_a1 x_a2] HasStuck.stuck := by
  have hn := eo__24mk_5farith_5fmult_5fsign_5fsgn.helper_3
  conv => lhs; unfold Eo.__eo_l_2___mk_arith_mult_sign_sgn
  unfold EoCases.__mk_arith_mult_sign_sgn.case_2
  logos_eq_deep

theorem eo__24mk_5farith_5fmult_5fsign_5fsgn.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___mk_arith_mult_sign_sgn x_a0 x_a1 x_a2 =
      firstSome [EoCases.__mk_arith_mult_sign_sgn.case_1 x_a0 x_a1 x_a2, EoCases.__mk_arith_mult_sign_sgn.case_2 x_a0 x_a1 x_a2, EoCases.__mk_arith_mult_sign_sgn.case_3 x_a0 x_a1 x_a2] HasStuck.stuck := by
  have hn := eo__24mk_5farith_5fmult_5fsign_5fsgn.helper_2
  conv => lhs; unfold Eo.__eo_l_1___mk_arith_mult_sign_sgn
  unfold EoCases.__mk_arith_mult_sign_sgn.case_1
  logos_eq_deep

/-- logos's `__mk_arith_mult_sign_sgn` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5farith_5fmult_5fsign_5fsgn.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_arith_mult_sign_sgn x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_arith_mult_sign_sgn.case_0 x_a0 x_a1 x_a2, EoCases.__mk_arith_mult_sign_sgn.case_1 x_a0 x_a1 x_a2, EoCases.__mk_arith_mult_sign_sgn.case_2 x_a0 x_a1 x_a2, EoCases.__mk_arith_mult_sign_sgn.case_3 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_arith_mult_sign_sgn
  unfold EoCases.__mk_arith_mult_sign_sgn.case_0
  have hn := eo__24mk_5farith_5fmult_5fsign_5fsgn.helper_1
  logos_eq_deep

theorem body_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5farith_5fmult_5fsign_5fsgn s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_mult_sign_sgn x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5farith_5fmult_5fsign_5fsgn.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5farith_5fmult_5fsign_5fsgn
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  case_step with case_3_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 hc3 in EoCases.__mk_arith_mult_sign_sgn.case_0 EoCases.__mk_arith_mult_sign_sgn.case_1 EoCases.__mk_arith_mult_sign_sgn.case_2 EoCases.__mk_arith_mult_sign_sgn.case_3

theorem eo__24mk_5farith_5fmult_5fsign_5fsgn_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5farith_5fmult_5fsign_5fsgn.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5farith_5fmult_5fsign_5fsgn
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 922#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5farith_5fmult_5fsign_5fsgn s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_arith_mult_sign_sgn x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_922 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_922 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5farith_5fmult_5fsign_5fsgn_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5farith_5fsum_5fub_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5farith_5fsum_5fub s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_sum_ub.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_sum_ub.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5farith_5fsum_5fub
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_sum_ub.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_sum_ub.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_and.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v13 dropping he_v14 hinv2 e_v14 s2
  store_step with Store.apply_rep s3 v11 v12 _ _ hinv3 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 h_v13 h_v14 dropping h_v11 hinv3 s3 v11
  store_step with Store.apply_rep s4 v15 v9 _ _ hinv4 h64 h_v15 h_v9 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v12 h_v13 h_v14 dropping h_v15 h_v9 hinv4 s4 v15 v9
  store_step with Store.apply_rep s5 v14 v16 _ _ hinv5 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v12 h_v13 dropping h_v14 h_v16 hinv5 s5 v14 v16
  store_step with Store.apply_rep s6 v17 v2 _ _ hinv6 h64 h_v17 h_v2 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v12 h_v13 dropping h_v17 h_v2 hinv6 s6 v17 v2
  step as ⟨e_v19, he_v19⟩
  store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s7 e_v19 (by rw [he_v19]; rfl) h_v13 h_v18 hinv7 h64 (hG.rem hrem) op_not_left_eo_and as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v12 dropping h_v13 h_v18 he_v19 hinv7 e_v19 s7 v13 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v12 h_v19 dropping he_v20 hinv8 e_v20 s8
  store_step with ih.eo__24eo_5ftypeof s9 v12 _ hinv9 h64 (hG.rem hrem) h_v12 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v12 h_v19 h_v20 dropping hinv9 s9
  store_step with ih.eo__24arith_5fmk_5fzero s10 v21 _ hinv10 h64 (hG.rem hrem) h_v21 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v12 h_v19 h_v20 dropping h_v21 hinv10 s10 v21
  store_step with Store.apply_mk_rep s11 v20 v22 _ _ hinv11 h64 h_v20 h_v22 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v12 h_v19 dropping h_v20 h_v22 hinv11 s11 v20 v22
  store_step with ih.eo__24eo_5ftypeof s12 v12 _ hinv12 h64 (hG.rem hrem) h_v12 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v19 h_v23 dropping h_v12 hinv12 s12 v12
  store_step with ih.eo__24arith_5fmk_5fzero s13 v24 _ hinv13 h64 (hG.rem hrem) h_v24 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v19 h_v23 dropping h_v24 hinv13 s13 v24
  store_step with Store.apply_mk_rep s14 v23 v25 _ _ hinv14 h64 h_v23 h_v25 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v19 dropping h_v23 h_v25 hinv14 s14 v23 v25
  store_step with ih.eo__24mk_5farith_5fsum_5fub_5frec s15 v19 v26 _ _ hinv15 h64 (hG.rem hrem) h_v19 h_v26 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying dropping h_v19 h_v26 hinv15 s15 v19 v26
  case_done hinv16 hG with h_v27 in EoCases.__mk_arith_sum_ub.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__mk_arith_sum_ub` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5farith_5fsum_5fub.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __mk_arith_sum_ub x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_arith_sum_ub.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __mk_arith_sum_ub
  unfold EoCases.__mk_arith_sum_ub.case_0
  logos_eq

theorem body_eo__24mk_5farith_5fsum_5fub_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24mk_5farith_5fsum_5fub s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_sum_ub x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5farith_5fsum_5fub.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24mk_5farith_5fsum_5fub
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24mk_5farith_5fsum_5fub_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__mk_arith_sum_ub.case_0

theorem eo__24mk_5farith_5fsum_5fub_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5farith_5fsum_5fub.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24mk_5farith_5fsum_5fub
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5farith_5fsum_5fub s1 a0) (fun s' t => Represents.rep s' t (__mk_arith_sum_ub x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5farith_5fsum_5fub_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5farith_5fsum_5fub_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5farith_5fsum_5fub_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_arith_sum_ub_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__mk_arith_sum_ub_rec.case_0 x_a0 x_a1 = some (__mk_arith_sum_ub_rec y0 y1)
      | core.result.Result.Ok none => EoCases.__mk_arith_sum_ub_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5farith_5fsum_5fub_5frec
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_0
  case_done hinv1 hG with h_a1 in EoCases.__mk_arith_sum_ub_rec.case_0 using hn_a0 hn_a1

theorem case_1_eo__24mk_5farith_5fsum_5fub_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5farith_5fsum_5fub_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_arith_sum_ub_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__mk_arith_sum_ub_rec.case_1 x_a0 x_a1 = some (__mk_arith_sum_ub_rec y0 y1)
      | core.result.Result.Ok none => EoCases.__mk_arith_sum_ub_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5farith_5fsum_5fub_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_sum_ub_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_a1 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v19 (by rw [he_v19]; exact empty_args) hinv1 h64 as ⟨v19, s2, hinv2, h_v19⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 h_v17 h_v18 dropping h_a1 h_v14 h_v4 h_v5 h_v6 h_v8 he_v19 hinv1 e_v19 s1 v14 v4 v5 v6 v8
  store_step with Store.apply_rep s2 v19 v12 _ _ hinv2 h64 h_v19 h_v12 (by ns_tac) (by ns_tac) as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_v2 h_v9 h_v11 h_v15 h_v17 h_v18 dropping h_v12 h_v19 hinv2 s2 v12 v19
  store_step with Store.apply_rep s3 v20 v18 _ _ hinv3 h64 h_v20 h_v18 (by ns_tac) (by ns_tac) as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_v2 h_v9 h_v11 h_v15 h_v17 dropping h_v18 h_v20 hinv3 s3 v18 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s4 e_v22 (by rw [he_v22]; exact empty_args) hinv4 h64 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v2 h_v9 h_v11 h_v15 h_v17 h_v21 dropping he_v22 hinv4 e_v22 s4
  store_step with Store.apply_rep s5 v22 v9 _ _ hinv5 h64 h_v22 h_v9 (by ns_tac) (by ns_tac) as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_v2 h_v11 h_v15 h_v17 h_v21 dropping h_v22 h_v9 hinv5 s5 v22 v9
  store_step with Store.apply_rep s6 v23 v15 _ _ hinv6 h64 h_v23 h_v15 (by ns_tac) (by ns_tac) as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_v2 h_v11 h_v17 h_v21 dropping h_v15 h_v23 hinv6 s6 v15 v23
  store_step with ih.eo__24arith_5frel_5fsum s7 v11 v17 v21 v24 _ _ _ _ hinv7 h64 (hG.rem hrem) h_v11 h_v17 h_v21 h_v24 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_v2 dropping h_v11 h_v17 h_v21 h_v24 hinv7 s7 v11 v17 v21 v24
  case_again hinv8 hG with h_v2 h_v25 in EoCases.__mk_arith_sum_ub_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v14 hn_v15 hn_v17 hn_v18

/-- logos's `__mk_arith_sum_ub_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5farith_5fsum_5fub_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_arith_sum_ub_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_arith_sum_ub_rec.case_0 x_a0 x_a1, EoCases.__mk_arith_sum_ub_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_arith_sum_ub_rec
  unfold EoCases.__mk_arith_sum_ub_rec.case_0 EoCases.__mk_arith_sum_ub_rec.case_1
  logos_eq

theorem step_eo__24mk_5farith_5fsum_5fub_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24mk_5farith_5fsum_5fub_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__mk_arith_sum_ub_rec x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __mk_arith_sum_ub_rec x_a0 x_a1 = __mk_arith_sum_ub_rec y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5farith_5fsum_5fub_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24mk_5farith_5fsum_5fub_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24mk_5farith_5fsum_5fub_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24mk_5farith_5fsum_5fub_5frec_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_arith_sum_ub_rec.case_0 EoCases.__mk_arith_sum_ub_rec.case_1

theorem body_eo__24mk_5farith_5fsum_5fub_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5farith_5fsum_5fub_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_sum_ub_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24mk_5farith_5fsum_5fub_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_sum_ub_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24mk_5farith_5fsum_5fub_5frec body_eo__24mk_5farith_5fsum_5fub_5frec_loop
  step with step_eo__24mk_5farith_5fsum_5fub_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24mk_5farith_5fsum_5fub_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24mk_5farith_5fsum_5fub_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5farith_5fsum_5fub_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5farith_5fsum_5fub_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 924#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5farith_5fsum_5fub_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_arith_sum_ub_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_924 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_924 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5farith_5fsum_5fub_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5farith_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5farith_5ftrichotomy s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_arith_trichotomy.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_arith_trichotomy.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5farith_5ftrichotomy
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_trichotomy.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_trichotomy.case_0
  pat_unapply h_a1 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__mk_arith_trichotomy.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__mk_arith_trichotomy.case_0
  pat_same v11 v5 with h_v11 h_v5 using hinv else hinv hG in EoCases.__mk_arith_trichotomy.case_0
  pat_same v8 v2 with h_v8 h_v2 using hinv else hinv hG in EoCases.__mk_arith_trichotomy.case_0
  store_step with ih.eo__24arith_5frel_5ftrichotomy s v4 v10 v5 v2 _ _ _ _ hinv h64 hrem h_v4 h_v10 h_v5 h_v2 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying dropping h_a0 h_a1 h_v1 h_v10 h_v11 h_v2 h_v4 h_v5 h_v7 h_v8 v1 v10 v11 v2 v4 v5 v7 v8
  case_done hinv1 hG with h_v12 in EoCases.__mk_arith_trichotomy.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__mk_arith_trichotomy` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5farith_5ftrichotomy.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_arith_trichotomy x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_arith_trichotomy.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_arith_trichotomy
  unfold EoCases.__mk_arith_trichotomy.case_0
  logos_eq

theorem body_eo__24mk_5farith_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5farith_5ftrichotomy s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_arith_trichotomy x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5farith_5ftrichotomy.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5farith_5ftrichotomy
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5farith_5ftrichotomy_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__mk_arith_trichotomy.case_0

theorem eo__24mk_5farith_5ftrichotomy_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5farith_5ftrichotomy.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5farith_5ftrichotomy
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5farith_5ftrichotomy s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_arith_trichotomy x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5farith_5ftrichotomy_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fcong_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_cong_rhs.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_cong_rhs.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fcong_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_cong_rhs.case_0
  pat_unapply h_a1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_cong_rhs.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__mk_cong_rhs.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_and.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v1 h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_a1 h_v4 he_v9 e_v9 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v16 (by rw [he_v16]; exact empty_args) hinv1 h64 as ⟨v16, s2, hinv2, h_v16⟩ growing hG carrying h_v1 h_v2 h_v5 h_v12 h_v14 h_v15 dropping h_v11 h_v7 h_v8 h_v9 he_v16 hinv1 e_v16 s1 v11 v7 v8 v9
  pat_same v14 v16 with h_v14 h_v16 using hinv2 else hinv2 hG in EoCases.__mk_cong_rhs.case_0
  pat_same v15 v2 with h_v15 h_v2 using hinv2 else hinv2 hG in EoCases.__mk_cong_rhs.case_0
  store_step with ih.eo__24mk_5fcong_5frhs s2 v1 v5 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v5 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_v12 dropping h_v1 h_v14 h_v15 h_v16 h_v2 h_v5 hinv2 s2 v1 v14 v15 v16 v2 v5
  store_step with Store.apply_mk_rep s3 v17 v12 _ _ hinv3 h64 h_v17 h_v12 as ⟨v18, s4, hinv4, h_v18⟩ growing hG carrying dropping h_v12 h_v17 hinv3 s3 v12 v17
  case_done hinv4 hG with h_v18 in EoCases.__mk_cong_rhs.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v11 hn_v12 hn_v14 hn_v15

theorem case_1_eo__24mk_5fcong_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_cong_rhs.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_cong_rhs.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fcong_5frhs
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_1
  case_done hinv1 hG with h_a0 in EoCases.__mk_cong_rhs.case_1 using hn_a0 hn_a1

/-- logos's fall-through helpers of `__mk_cong_rhs`, each the program's cases from its first on. -/
theorem eo__24mk_5fcong_5frhs.helper_1 (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___mk_cong_rhs x_a0 x_a1 =
      firstSome [EoCases.__mk_cong_rhs.case_1 x_a0 x_a1] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___mk_cong_rhs
  unfold EoCases.__mk_cong_rhs.case_1
  logos_eq_deep

/-- logos's `__mk_cong_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fcong_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_cong_rhs x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_cong_rhs.case_0 x_a0 x_a1, EoCases.__mk_cong_rhs.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_cong_rhs
  unfold EoCases.__mk_cong_rhs.case_0
  have hn := eo__24mk_5fcong_5frhs.helper_1
  logos_eq_deep

theorem body_eo__24mk_5fcong_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_cong_rhs x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fcong_5frhs.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fcong_5frhs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fcong_5frhs_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fcong_5frhs_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_cong_rhs.case_0 EoCases.__mk_cong_rhs.case_1

theorem eo__24mk_5fcong_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fcong_5frhs.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fcong_5frhs
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 926#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5fcong_5frhs s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_cong_rhs x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_926 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_926 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fcong_5frhs_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdistinct_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdistinct_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_distinct_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_distinct_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdistinct_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_distinct.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_0
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v6 h_v8 h_v9 dropping h_v1 h_v2 h_v3 h_v5 he_v10 hinv1 e_v10 s1 v1 v2 v3 v5
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__mk_distinct_elim.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_distinct.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v6 h_v9 dropping h_v10 h_v8 he_v11 hinv2 e_v11 s2 v10 v8
  store_step with Store.apply_rep s3 v11 v6 _ _ hinv3 h64 h_v11 h_v6 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v6 h_v9 dropping h_v11 hinv3 s3 v11
  store_step with ih.eo__24mk_5fdistinct_5felim s4 v12 _ hinv4 h64 (hG.rem hrem) h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v6 h_v9 dropping h_v12 hinv4 s4 v12
  store_step with ih.eo__24mk_5fdistinct_5felim_5frec s5 v9 v6 v13 _ _ _ hinv5 h64 (hG.rem hrem) h_v9 h_v6 h_v13 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying dropping h_v13 h_v6 h_v9 hinv5 s5 v13 v6 v9
  case_done hinv6 hG with h_v14 in EoCases.__mk_distinct_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v8 hn_v9

theorem case_1_eo__24mk_5fdistinct_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdistinct_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_distinct_elim.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_distinct_elim.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdistinct_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_distinct.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 hinv1 s1 v1 v3
  case_done hinv2 hG with h_v4 in EoCases.__mk_distinct_elim.case_1 using hn_a0 hn_v1 hn_v2

/-- logos's `__mk_distinct_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdistinct_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __mk_distinct_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_distinct_elim.case_0 x_a0, EoCases.__mk_distinct_elim.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __mk_distinct_elim
  unfold EoCases.__mk_distinct_elim.case_0 EoCases.__mk_distinct_elim.case_1
  logos_eq

theorem body_eo__24mk_5fdistinct_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24mk_5fdistinct_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_distinct_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdistinct_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24mk_5fdistinct_5felim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24mk_5fdistinct_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24mk_5fdistinct_5felim_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__mk_distinct_elim.case_0 EoCases.__mk_distinct_elim.case_1

theorem eo__24mk_5fdistinct_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdistinct_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24mk_5fdistinct_5felim
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 927#u32 _ [a0] rfl
    (fun s1 => body_eo__24mk_5fdistinct_5felim s1 a0) (fun s' t => Represents.rep s' t (__mk_distinct_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_927 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_927 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdistinct_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdistinct_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdistinct_5felim_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_distinct_elim_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_distinct_elim_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdistinct_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim_rec.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim_rec.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim_rec.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 a0 _ _ hinv4 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v8 dropping h_v10 h_v5 hinv5 s5 v10 v5
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  store_step with Store.apply_rep s7 v7 v12 _ _ hinv7 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_v12 h_v7 hinv7 s7 v12 v7
  store_step with ih.eo__24mk_5fdistinct_5felim_5frec s8 a0 v2 a2 _ _ _ hinv8 h64 (hG.rem hrem) h_a0 h_v2 h_a2 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v13 dropping h_a0 h_a2 h_v2 hinv8 s8 v2
  store_step with Store.apply_mk_rep s9 v13 v14 _ _ hinv9 h64 h_v13 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying dropping h_v13 h_v14 hinv9 s9 v13 v14
  case_done hinv10 hG with h_v15 in EoCases.__mk_distinct_elim_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fdistinct_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdistinct_5felim_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_distinct_elim_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_distinct_elim_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdistinct_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim_rec.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a2 h_v1 dropping h_a1 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim_rec.case_1
  case_done hinv1 hG with h_a2 in EoCases.__mk_distinct_elim_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__mk_distinct_elim_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdistinct_5felim_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_distinct_elim_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_distinct_elim_rec.case_0 x_a0 x_a1 x_a2, EoCases.__mk_distinct_elim_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_distinct_elim_rec
  unfold EoCases.__mk_distinct_elim_rec.case_0 EoCases.__mk_distinct_elim_rec.case_1
  logos_eq

theorem body_eo__24mk_5fdistinct_5felim_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fdistinct_5felim_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_distinct_elim_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdistinct_5felim_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5fdistinct_5felim_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5fdistinct_5felim_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5fdistinct_5felim_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_distinct_elim_rec.case_0 EoCases.__mk_distinct_elim_rec.case_1

theorem eo__24mk_5fdistinct_5felim_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdistinct_5felim_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fdistinct_5felim_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 928#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5fdistinct_5felim_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_distinct_elim_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_928 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_928 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdistinct_5felim_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_collapse_updater_rhs.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_collapse_updater_rhs.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_collapse_updater_rhs.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_collapse_updater_rhs.case_0
  pat_destruct CtorSpec.eo_update.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__mk_dt_collapse_updater_rhs.case_0
  obtain hn_v7 := CtorSpec.eo_update.fields_ne_stuck hinv h_v4
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_a0 h_v1 h_v4 he_v8 e_v8 v1 v4
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping hinv1 s1
  store_step with ih.eo__24dt_5fget_5fselectors_5fof_5fapp s2 v9 v5 _ _ hinv2 h64 (hG.rem hrem) h_v9 h_v5 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv2 s2 v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s3 e_v11 (by rw [he_v11]; rfl) h_v8 h_v10 h_v7 hinv3 h64 (hG.rem hrem) (by not_left_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v10 h_v8 he_v11 hinv3 e_v11 s3 v10 v8
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_is_neg s4 e_v12 (by rw [he_v12]; rfl) h_v11 hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 he_v12 hinv4 e_v12 s4 v11
  have h_ite_v26 := (show if_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s5 v12 v5 v7 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    rcases Store.boolean_value_term h_v12 with ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩ | ⟨hx_13, hbv_13⟩
    · ite_branch hbv_13
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_13 h_v5)
    · ite_branch hbv_13
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v12 he_v13 e_v13 v12
      store_step with ih.eo__24eo_5ftypeof s6 v5 _ hinv6 h64 (hG.rem hrem) h_v5 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 dropping
      store_step with ih.eo__24dt_5fget_5fselectors_5fof_5fapp s7 v14 v5 _ _ hinv7 h64 (hG.rem hrem) h_v14 h_v5 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 dropping h_v14 hinv7 s7 v14
      step as ⟨e_v16, he_v16⟩
      store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s8 e_v16 (by rw [he_v16]; rfl) h_v13 h_v15 hinv8 h64 (hG.rem hrem) (by not_left_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v13 h_v15 he_v16 hinv8 e_v16 s8 v13 v15
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s9 e_v17 (by rw [he_v17]; exact empty_args) hinv9 h64 as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying h_v2 h_v5 h_v7 h_v16 dropping he_v17 hinv9 e_v17 s9
      store_step with ih.eo__24eo_5ftypeof s10 v5 _ hinv10 h64 (hG.rem hrem) h_v5 as ⟨v18, s11, hinv11, h_v18⟩ growing hG carrying h_v2 h_v5 h_v7 h_v16 h_v17 dropping hinv10 s10
      store_step with ih.eo__24dt_5fget_5fselectors_5fof_5fapp s11 v18 v5 _ _ hinv11 h64 (hG.rem hrem) h_v18 h_v5 as ⟨v19, s12, hinv12, h_v19⟩ growing hG carrying h_v2 h_v5 h_v7 h_v16 h_v17 dropping h_v18 hinv11 s11 v18
      step as ⟨e_v20, he_v20⟩
      store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s12 e_v20 (by rw [he_v20]; rfl) h_v17 h_v19 h_v7 hinv12 h64 (hG.rem hrem) (by not_left_tac) as ⟨v20, s13, hinv13, h_v20⟩ growing hG carrying h_v2 h_v5 h_v16 dropping h_v17 h_v19 h_v7 he_v20 hinv12 e_v20 s12 v17 v19 v7
      step as ⟨e_v21, he_v21⟩
      store_step with Store.builtin_spec_neg s13 e_v21 (by rw [he_v21]; rfl) h_v20 hinv13 h64 as ⟨v21, s14, hinv14, h_v21⟩ growing hG carrying h_v2 h_v5 h_v16 dropping h_v20 he_v21 hinv13 e_v21 s13 v20
      step as ⟨e_v22, he_v22⟩
      store_step with Store.builtin_spec_add s14 e_v22 (by rw [he_v22]; rfl) h_v16 h_v21 hinv14 h64 as ⟨v22, s15, hinv15, h_v22⟩ growing hG carrying h_v2 h_v5 dropping h_v16 h_v21 he_v22 hinv14 e_v22 s14 v16 v21
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s15 1#u32 (-1) (by scalar_tac) hinv15 h64 as ⟨v23, s16, hinv16, h_v23⟩ growing hG carrying h_v2 h_v5 h_v22 dropping hinv15 s15
      step as ⟨e_v24, he_v24⟩
      store_step with Store.builtin_spec_add s16 e_v24 (by rw [he_v24]; rfl) h_v22 h_v23 hinv16 h64 as ⟨v24, s17, hinv17, h_v24⟩ growing hG carrying h_v2 h_v5 dropping h_v22 h_v23 he_v24 hinv16 e_v24 s16 v22 v23
      store_step with ih.eo__24dt_5fcollapse_5fupdater_5frhs s17 v5 v2 v24 _ _ _ hinv17 h64 (hG.rem hrem) h_v5 h_v2 h_v24 as ⟨v25, s18, hinv18, h_v25⟩ growing hG carrying dropping h_v2 h_v24 h_v5 hinv17 s17 v2 v24 v5
      ite_done hinv18 hG with (eo_ite_false_rep _ hx_13 h_v25)
    · ite_branch hbv_13
      ite_stuck hinv5 hG with hx_13)
  store_step with h_ite_v26 as ⟨v26, s6, hinv6, h_v26⟩ growing hG carrying dropping h_ite_v26 h_v12 h_v2 h_v5 h_v7 hinv5 s5 v12 v2 v5 v7
  case_done hinv6 hG with h_v26 in EoCases.__mk_dt_collapse_updater_rhs.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

theorem case_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_collapse_updater_rhs.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_collapse_updater_rhs.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_collapse_updater_rhs.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_collapse_updater_rhs.case_1
  pat_destruct CtorSpec.eo_tuple_2eupdate.destruct h_v4 as ⟨v7, x_v7, h_v7⟩ else hinv hG in EoCases.__mk_dt_collapse_updater_rhs.case_1
  obtain hn_v7 := CtorSpec.eo_tuple_2eupdate.fields_ne_stuck hinv h_v4
  store_step with ih.eo__24tuple_5fcollapse_5fupdater_5frhs s v5 v2 v7 _ _ _ hinv h64 hrem h_v5 h_v2 h_v7 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying dropping h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 v1 v2 v4 v5 v7
  case_done hinv1 hG with h_v8 in EoCases.__mk_dt_collapse_updater_rhs.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7

/-- logos's `__mk_dt_collapse_updater_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5fcollapse_5fupdater_5frhs.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __mk_dt_collapse_updater_rhs x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_collapse_updater_rhs.case_0 x_a0, EoCases.__mk_dt_collapse_updater_rhs.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_collapse_updater_rhs
  unfold EoCases.__mk_dt_collapse_updater_rhs.case_0 EoCases.__mk_dt_collapse_updater_rhs.case_1
  logos_eq

theorem body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_collapse_updater_rhs x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5fcollapse_5fupdater_5frhs.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__mk_dt_collapse_updater_rhs.case_0 EoCases.__mk_dt_collapse_updater_rhs.case_1

theorem eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5fcollapse_5fupdater_5frhs.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24mk_5fdt_5fcollapse_5fupdater_5frhs
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s1 a0) (fun s' t => Represents.rep s' t (__mk_dt_collapse_updater_rhs x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdt_5fcons_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5fcons_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_cons_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_cons_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5fcons_5feq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_cons_eq.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_cons_eq.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_dt_cons_eq.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_dt_cons_eq.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_dt_cons_eq.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a1 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_dt_cons_eq.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 dropping he_v15 hinv3 e_v15 s3
  store_step with Store.apply_rep s4 v15 v5 _ _ hinv4 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 h_v14 dropping h_v15 h_v5 hinv4 s4 v15 v5
  store_step with Store.apply_rep s5 v16 v12 _ _ hinv5 h64 h_v16 h_v12 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v14 dropping h_v12 h_v16 hinv5 s5 v12 v16
  store_step with Store.apply_rep s6 v14 v17 _ _ hinv6 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 dropping h_v14 h_v17 hinv6 s6 v14 v17
  store_step with ih.eo__24mk_5fdt_5fcons_5feq s7 v2 v9 _ _ hinv7 h64 (hG.rem hrem) h_v2 h_v9 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v18 dropping h_v2 h_v9 hinv7 s7 v2 v9
  store_step with Store.apply_mk_rep s8 v18 v19 _ _ hinv8 h64 h_v18 h_v19 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying dropping h_v18 h_v19 hinv8 s8 v18 v19
  case_done hinv9 hG with h_v20 in EoCases.__mk_dt_cons_eq.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24mk_5fdt_5fcons_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5fcons_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_cons_eq.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_cons_eq.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5fcons_5feq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_cons_eq.case_1
  pat_unapply h_a1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_cons_eq.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v1 h_v2 h_v4 h_v5 dropping h_a0 h_a1 he_v6 e_v6
  store_step with ih.eo__24mk_5fdt_5fcons_5feq s1 v1 v4 _ _ hinv1 h64 (hG.rem hrem) h_v1 h_v4 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_v1 h_v4 hinv1 s1 v1 v4
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_and.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v6 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v6 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v5 h_v6 h_v7 h_v8 dropping h_v2 h_v9 hinv4 s4 v2 v9
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v6 h_v7 h_v8 dropping h_v10 h_v5 hinv5 s5 v10 v5
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v6 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v6 h_v7 h_v12 dropping hinv7 s7
  store_step with Store.apply_rep s8 v12 v13 _ _ hinv8 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v6 h_v7 dropping h_v12 h_v13 hinv8 s8 v12 v13
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s9 e_v15 (by rw [he_v15]; rfl) h_v6 h_v7 h_v14 hinv9 h64 (hG.rem hrem) op_not_left_eo_and op_unique_nil_eo_and as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying dropping h_v14 h_v6 h_v7 he_v15 hinv9 e_v15 s9 v14 v6 v7
  case_done hinv10 hG with h_v15 in EoCases.__mk_dt_cons_eq.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24mk_5fdt_5fcons_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24mk_5fdt_5fcons_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_cons_eq.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_cons_eq.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24mk_5fdt_5fcons_5feq
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__mk_dt_cons_eq.case_2
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping h_a1 he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_eq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 dropping h_v0 he_v1 hinv1 e_v1 s1 v0
  have h_ite_v9 := (show if_2_eo__24mk_5fdt_5fcons_5feq s2 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24mk_5fdt_5fcons_5feq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 dropping h_v1 v1
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo_tuple_2eunit.construct s2 e_v3 (by rw [he_v3]; exact empty_args) hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 dropping h_v1 he_v3 e_v3 v1
      step as ⟨e_v4, he_v4⟩
      store_step with Store.builtin_spec_is_eq s3 e_v4 (by rw [he_v4]; rfl) h_a0 h_v3 hinv3 h64 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying h_a0 dropping h_v3 he_v4 e_v4 v3
      have h_ite_v8 := (show if_1_eo__24mk_5fdt_5fcons_5feq s4 v4 a0 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24mk_5fdt_5fcons_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
        · ite_branch hbv_5
          store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v5, s5, hinv5, h_v5⟩ growing hG carrying h_a0 dropping h_v4 v4
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_5 h_v5)
        · ite_branch hbv_5
          store_step with ih.eo__24eo_5fdt_5fselectors s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v6, s5, hinv5, h_v6⟩ growing hG carrying dropping h_a0 h_v4 v4
          step as ⟨e_v7, he_v7⟩
          store_step with Store.builtin_spec_is_ok s5 e_v7 (by rw [he_v7]; rfl) h_v6 hinv5 h64 as ⟨v7, s6, hinv6, h_v7⟩ growing hG carrying dropping h_v6 he_v7 e_v7 v6
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_5 h_v7)
        · ite_branch hbv_5
          ite_stuck hinv4 hG with hx_5)
      store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying dropping h_a0 h_ite_v8 h_v4 v4
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_2 h_v8)
    · ite_branch hbv_2
      ite_stuck hinv2 hG with hx_2)
  store_step with h_ite_v9 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying dropping h_a0 h_ite_v9 h_v1 hinv2 s2 v1
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_v9 dropping hinv3 s3
  have h_req_v12 := (show requires_3_eo__24mk_5fdt_5fcons_5feq s4 v9 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_3_eo__24mk_5fdt_5fcons_5feq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v9 v10 with h_v9 h_v10 using hinv4 hG
    req_stuck h_v9 as hq_v9 using hinv4 hG
    store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying dropping h_v10 h_v9 hinv4 s4 v10 v9
    req_done hinv5 hG with h_v11 using hq_v9)
  store_step with h_req_v12 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying dropping h_req_v12 h_v10 h_v9 hinv4 s4 v10 v9
  case_done hinv6 hG with h_v12 in EoCases.__mk_dt_cons_eq.case_2 using hn_a0 hn_a1

/-- logos's `__mk_dt_cons_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5fcons_5feq.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_dt_cons_eq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_cons_eq.case_0 x_a0 x_a1, EoCases.__mk_dt_cons_eq.case_1 x_a0 x_a1, EoCases.__mk_dt_cons_eq.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_cons_eq
  unfold EoCases.__mk_dt_cons_eq.case_0 EoCases.__mk_dt_cons_eq.case_1 EoCases.__mk_dt_cons_eq.case_2
  logos_eq

theorem body_eo__24mk_5fdt_5fcons_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fdt_5fcons_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_cons_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5fcons_5feq.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fdt_5fcons_5feq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fdt_5fcons_5feq_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fdt_5fcons_5feq_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  case_step with case_2_eo__24mk_5fdt_5fcons_5feq_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__mk_dt_cons_eq.case_0 EoCases.__mk_dt_cons_eq.case_1 EoCases.__mk_dt_cons_eq.case_2

theorem eo__24mk_5fdt_5fcons_5feq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5fcons_5feq.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fdt_5fcons_5feq
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 930#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5fdt_5fcons_5feq s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_dt_cons_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_930 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_930 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5fcons_5feq_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdt_5finst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5finst s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5finst
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_inst.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_inst.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a1 h_a2 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  pat_same a1 v7 with h_a1 h_v7 using hinv2 else hinv2 hG in EoCases.__mk_dt_inst.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_Tuple.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a2 h_v2 h_v5 dropping h_a1 h_v7 he_v8 hinv2 e_v8 s2 v7
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a2 h_v2 dropping h_v5 h_v8 hinv3 s3 v5 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a2 dropping h_v2 h_v9 hinv4 s4 v2 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a2 h_v10 dropping hinv5 s5
  store_step with ih.eo__24mk_5fdt_5finst_5ftuple_5frec s6 v10 a2 v11 _ _ _ hinv6 h64 (hG.rem hrem) h_v10 h_a2 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying dropping h_a2 h_v10 h_v11 hinv6 s6 v10 v11
  case_done hinv7 hG with h_v12 in EoCases.__mk_dt_inst.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fdt_5finst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5finst s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5finst
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__mk_dt_inst.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__mk_dt_inst.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24mk_5fdt_5finst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24mk_5fdt_5finst s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24mk_5fdt_5finst
  have hG := Store.Grows.refl s
  store_step with ih.eo__24dt_5fget_5fselectors s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with ih.eo__24eo_5fdt_5fconstructors s2 a0 _ hinv2 h64 (hG.rem hrem) h_a0 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping hinv2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with ih.eo__24dt_5fget_5fconstructors s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 dropping h_a0 hinv4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s5 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 h_a1 hinv5 h64 (hG.rem hrem) (by not_left_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a2 h_v0 h_v1 h_v2 dropping h_a1 h_v3 h_v4 he_v5 hinv5 e_v5 s5 v3 v4
  store_step with ih.eo__24assoc_5fnil_5fnth s6 v1 v2 v5 _ _ _ hinv6 h64 (hG.rem hrem) h_v1 h_v2 h_v5 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a2 h_v0 dropping h_v1 h_v2 h_v5 hinv6 s6 v1 v2 v5
  store_step with ih.eo__24mk_5fdt_5finst_5frec s7 v0 a2 v6 _ _ _ hinv7 h64 (hG.rem hrem) h_v0 h_a2 h_v6 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_a2 h_v0 h_v6 hinv7 s7 v0 v6
  case_done hinv8 hG with h_v7 in EoCases.__mk_dt_inst.case_2 using hn_a0 hn_a1 hn_a2

/-- logos's `__mk_dt_inst` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5finst.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_dt_inst x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_inst.case_0 x_a0 x_a1 x_a2, EoCases.__mk_dt_inst.case_1 x_a0 x_a1 x_a2, EoCases.__mk_dt_inst.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_inst
  unfold EoCases.__mk_dt_inst.case_0 EoCases.__mk_dt_inst.case_1 EoCases.__mk_dt_inst.case_2
  logos_eq

theorem body_eo__24mk_5fdt_5finst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fdt_5finst s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5finst.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5fdt_5finst
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5fdt_5finst_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5fdt_5finst_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24mk_5fdt_5finst_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 in EoCases.__mk_dt_inst.case_0 EoCases.__mk_dt_inst.case_1 EoCases.__mk_dt_inst.case_2

theorem eo__24mk_5fdt_5finst_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5finst.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fdt_5finst
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fdt_5finst s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_dt_inst x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5finst_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
