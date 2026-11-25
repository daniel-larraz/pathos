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

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_idem.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_idem.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_idem.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_idem` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_idem x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_idem.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_idem
  unfold EoCases.__eo_prog_str_to_lower_idem.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_idem x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_idem.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2didem
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_idem x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_len.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_len.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_len.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_len x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_len.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_len
  unfold EoCases.__eo_prog_str_to_lower_len.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_len x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_len.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_len x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_upper.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_upper.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_upper.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_upper` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_upper x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_upper.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_upper
  unfold EoCases.__eo_prog_str_to_lower_upper.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_upper x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_upper.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_upper x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_concat.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_concat.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat more_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat more_1_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v17 a1 _ _ hinv18 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v18 a2 _ _ hinv19 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s20 e_v20 (by rw [he_v20]; rfl) h_v16 h_v19 hinv20 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s21 v15 v20 _ _ hinv21 h64 h_v15 h_v20 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_mk_rep s22 v14 v21 _ _ hinv22 h64 h_v14 h_v21 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s23 _ _ rfl hinv23 h64 as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_mk_rep s24 v22 v23 _ _ hinv24 h64 h_v22 h_v23 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_mk_rep s25 v13 v24 _ _ hinv25 h64 h_v13 h_v24 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_mk_rep s26 v9 v25 _ _ hinv26 h64 h_v9 h_v25 as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  case_done hinv27 hG with h_v26 in EoCases.__eo_prog_str_to_upper_concat.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_str_to_upper_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_to_upper_concat x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_concat.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_concat
  unfold EoCases.__eo_prog_str_to_upper_concat.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_concat x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_to_upper_concat.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_concat x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_from_int.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_from_int.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_from_int.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_from_int` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_from_int x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_from_int.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_from_int
  unfold EoCases.__eo_prog_str_to_upper_from_int.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_from_int x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_from_int.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_from_int x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_idem.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_idem.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_idem.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_idem` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_idem x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_idem.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_idem
  unfold EoCases.__eo_prog_str_to_upper_idem.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_idem x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_idem.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2didem
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_idem x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_len.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_len.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_len.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_len x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_len.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_len
  unfold EoCases.__eo_prog_str_to_upper_len.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_len x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_len.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_len x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_lower.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_lower.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_lower.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_lower` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_lower x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_lower.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_lower
  unfold EoCases.__eo_prog_str_to_upper_lower.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_lower x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_lower.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_lower x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_concat_fit0.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_concat_fit0.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 more_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 more_1_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v11, x_v11, h_v11⟩ else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v11 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v18 (by rw [he_v18]; exact empty_args) hinv2 h64 as ⟨v18, s3, hinv3, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17
  pat_same v16 v18 with h_v16 h_v18 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_same v21 a0 with h_v21 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v14 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v29 (by rw [he_v29]; exact empty_args) hinv7 h64 as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s8 v29 a0 _ _ hinv8 h64 h_v29 h_a0 (by ns_tac) (by ns_tac) as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s9 v30 a1 _ _ hinv9 h64 h_v30 h_a1 (by ns_tac) (by ns_tac) as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s10 v28 v31 _ _ hinv10 h64 h_v28 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s11, hinv11, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s11 v32 a2 _ _ hinv11 h64 h_v32 h_a2 (by ns_tac) (by ns_tac) as ⟨v33, s12, hinv12, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s12 v33 a3 _ _ hinv12 h64 h_v33 h_a3 (by ns_tac) (by ns_tac) as ⟨v34, s13, hinv13, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s13 v27 v34 _ _ hinv13 h64 h_v27 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s14, hinv14, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v36 (by rw [he_v36]; exact empty_args) hinv14 h64 as ⟨v36, s15, hinv15, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s15 e_v37 (by rw [he_v37]; exact empty_args) hinv15 h64 as ⟨v37, s16, hinv16, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s16 v37 a3 _ _ hinv16 h64 h_v37 h_a3 (by ns_tac) (by ns_tac) as ⟨v38, s17, hinv17, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s17 v38 a1 _ _ hinv17 h64 h_v38 h_a1 (by ns_tac) (by ns_tac) as ⟨v39, s18, hinv18, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s18 e_v40 (by rw [he_v40]; rfl) h_v36 h_v39 hinv18 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v40, s19, hinv19, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_mk_rep s19 v35 v40 _ _ hinv19 h64 h_v35 h_v40 as ⟨v41, s20, hinv20, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  case_done hinv20 hG with h_v41 in EoCases.__eo_prog_str_update_concat_fit0.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v13 hn_v14 hn_v16 hn_v17 hn_v20 hn_v21 hn_v24 hn_v25

/-- logos's `__eo_prog_str_update_concat_fit0` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_concat_fit0.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_concat_fit0
  unfold EoCases.__eo_prog_str_update_concat_fit0.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_update_concat_fit0.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_fit.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_fit.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit more_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit more_1_eo__24eo_5fprog_5fstr_2dupdate_2dfit
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_fit.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v11, x_v11, h_v11⟩ else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v11 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v18 (by rw [he_v18]; exact empty_args) hinv2 h64 as ⟨v18, s3, hinv3, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17
  pat_same v16 v18 with h_v16 h_v18 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_same v21 a0 with h_v21 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v14 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_same v25 a2 with h_v25 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s7 v28 a0 _ _ hinv7 h64 h_v28 h_a0 (by ns_tac) (by ns_tac) as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s8 v29 a1 _ _ hinv8 h64 h_v29 h_a1 (by ns_tac) (by ns_tac) as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s9 v30 a2 _ _ hinv9 h64 h_v30 h_a2 (by ns_tac) (by ns_tac) as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s10 v27 v31 _ _ hinv10 h64 h_v27 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s11, hinv11, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s11 v32 a2 _ _ hinv11 h64 h_v32 h_a2 (by ns_tac) (by ns_tac) as ⟨v33, s12, hinv12, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  case_done hinv12 hG with h_v33 in EoCases.__eo_prog_str_update_fit.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v13 hn_v14 hn_v16 hn_v17 hn_v20 hn_v21 hn_v24 hn_v25

/-- logos's `__eo_prog_str_update_fit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2dfit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_fit.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_fit
  unfold EoCases.__eo_prog_str_update_fit.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2dfit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2dfit.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2dfit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_update_fit.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2dfit.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2dupdate_2dfit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2dfit s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_oob.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_oob.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob more_0_eo__24eo_5fprog_5fstr_2dupdate_2doob more_1_eo__24eo_5fprog_5fstr_2dupdate_2doob
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_same v21 a0 with h_v21 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_oob.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22
  pat_same v15 v23 with h_v15 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_oob.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23
  pat_same v4 v24 with h_v4 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v25 (by rw [he_v25]; exact empty_args) hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s7 v26 a0 _ _ hinv7 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s8 v27 a1 _ _ hinv8 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s9 v28 a2 _ _ hinv9 h64 h_v28 h_a2 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s10 v25 v29 _ _ hinv10 h64 h_v25 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s11 v30 a0 _ _ hinv11 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  case_done hinv12 hG with h_v31 in EoCases.__eo_prog_str_update_oob.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15 hn_v17 hn_v18 hn_v20 hn_v21

/-- logos's `__eo_prog_str_update_oob` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2doob.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_oob.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_oob
  unfold EoCases.__eo_prog_str_update_oob.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2doob s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2doob.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2doob
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_update_oob.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2doob_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2doob.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dupdate_2doob
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2doob s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_rev.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_rev.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev more_0_eo__24eo_5fprog_5fstr_2dupdate_2drev more_1_eo__24eo_5fprog_5fstr_2dupdate_2drev more_2_eo__24eo_5fprog_5fstr_2dupdate_2drev
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_same v18 a2 with h_v18 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_rev.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_rev.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  pat_same v4 v21 with h_v4 h_v21 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2erev.construct s7 e_v24 (by rw [he_v24]; exact empty_args) hinv7 h64 as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s9 v23 v25 _ _ hinv9 h64 h_v23 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s10 v26 a1 _ _ hinv10 h64 h_v26 h_a1 (by ns_tac) (by ns_tac) as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s11 v27 a2 _ _ hinv11 h64 h_v27 h_a2 (by ns_tac) (by ns_tac) as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s12 v22 v28 _ _ hinv12 h64 h_v22 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2erev.construct s13 e_v30 (by rw [he_v30]; exact empty_args) hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s14 e_v31 (by rw [he_v31]; exact empty_args) hinv14 h64 as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s15 v31 a0 _ _ hinv15 h64 h_v31 h_a0 (by ns_tac) (by ns_tac) as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__2d.construct s16 e_v33 (by rw [he_v33]; exact empty_args) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_str_2elen.construct s17 e_v34 (by rw [he_v34]; exact empty_args) hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s18 v34 a0 _ _ hinv18 h64 h_v34 h_a0 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s19 v33 v35 _ _ hinv19 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__2b.construct s20 e_v37 (by rw [he_v37]; exact empty_args) hinv20 h64 as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s21 v37 a1 _ _ hinv21 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__2b.construct s22 e_v39 (by rw [he_v39]; exact empty_args) hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s23 1#u32 (1) (by scalar_tac) hinv23 h64 as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s24 v39 v40 _ _ hinv24 h64 h_v39 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s26 v41 v42 _ _ hinv26 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s27 v38 v43 _ _ hinv27 h64 h_v38 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s28 v36 v44 _ _ hinv28 h64 h_v36 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s29 v32 v45 _ _ hinv29 h64 h_v32 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s30 v46 a2 _ _ hinv30 h64 h_v46 h_a2 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s31 v30 v47 _ _ hinv31 h64 h_v30 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s32 v29 v48 _ _ hinv32 h64 h_v29 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  case_done hinv33 hG with h_v49 in EoCases.__eo_prog_str_update_rev.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_str_update_rev` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2drev.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_rev.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_rev
  unfold EoCases.__eo_prog_str_update_rev.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2drev s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2drev.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2drev
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_update_rev.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2drev_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2drev.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dupdate_2drev
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2drev s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5fcode_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstring_5fcode_5finj s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_code_inj.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_code_inj.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5fcode_5finj more_0_eo__24eo_5fprog_5fstring_5fcode_5finj more_1_eo__24eo_5fprog_5fstring_5fcode_5finj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s5 1#u32 (-1) (by scalar_tac) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_or.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_not.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v13 v15 _ _ hinv16 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v9 v16 _ _ hinv17 h64 h_v9 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v8 v17 _ _ hinv18 h64 h_v8 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_or.construct s19 e_v19 (by rw [he_v19]; exact empty_args) hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v20 (by rw [he_v20]; exact empty_args) hinv20 h64 as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v20 a0 _ _ hinv21 h64 h_v20 h_a0 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v21 a1 _ _ hinv22 h64 h_v21 h_a1 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v19 v22 _ _ hinv23 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.literal_boolean_spec s24 false hinv24 h64 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s25 v23 v24 _ _ hinv25 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s26 v18 v25 _ _ hinv26 h64 h_v18 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s27 v7 v26 _ _ hinv27 h64 h_v7 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  case_done hinv28 hG with h_v27 in EoCases.__eo_prog_string_code_inj.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_string_code_inj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5fcode_5finj.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_string_code_inj x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_string_code_inj.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_code_inj
  unfold EoCases.__eo_prog_string_code_inj.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5fcode_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstring_5fcode_5finj s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_code_inj x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5fcode_5finj.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstring_5fcode_5finj
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstring_5fcode_5finj_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_string_code_inj.case_0

theorem eo__24eo_5fprog_5fstring_5fcode_5finj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5fcode_5finj.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstring_5fcode_5finj
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5fcode_5finj s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_string_code_inj x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5fcode_5finj_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_length_non_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_length_non_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_string_length_non_empty.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_string_length_non_empty.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  store_step with ih.eo__24str_5fis_5fempty s2 v8 _ hinv2 h64 (hG.rem hrem) h_v8 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  have h_req_v23 := (show requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s4 v13 v14 v11 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v13 v14 with h_v13 h_v14 using hinv4 hG
    req_stuck h_v13 as hq_v13 using hinv4 hG
    step as ⟨e_v15, he_v15⟩
    store_step with CtorSpec.eo_not.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo_str_2elen.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
    store_step with Store.apply_rep s7 v17 v11 _ _ hinv7 h64 h_v17 h_v11 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
    store_step with Store.apply_rep s8 v16 v18 _ _ hinv8 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
    store_step with Store.apply_rep s10 v19 v20 _ _ hinv10 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
    store_step with Store.apply_rep s11 v15 v21 _ _ hinv11 h64 h_v15 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
    req_done hinv12 hG with h_v22 using hq_v13)
  store_step with h_req_v23 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv13 hG with h_v23 in EoCases.__eo_prog_string_length_non_empty.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_string_length_non_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_length_non_empty x_a0 =
      (firstSome [EoCases.__eo_prog_string_length_non_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_length_non_empty
  unfold EoCases.__eo_prog_string_length_non_empty.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_length_non_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_string_length_non_empty.case_0

theorem eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_length_non_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_seq_unit_inj.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_seq_unit_inj.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj more_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v4 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15
  pat_same v14 v16 with h_v14 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s4 v17 v11 _ _ hinv4 h64 h_v17 h_v11 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s5 v18 v15 _ _ hinv5 h64 h_v18 h_v15 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv6 hG with h_v19 in EoCases.__eo_prog_string_seq_unit_inj.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15

/-- logos's `__eo_prog_string_seq_unit_inj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_seq_unit_inj x_a0 =
      (firstSome [EoCases.__eo_prog_string_seq_unit_inj.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_seq_unit_inj
  unfold EoCases.__eo_prog_string_seq_unit_inj.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_seq_unit_inj x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_string_seq_unit_inj.case_0

theorem eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5fseq_5funit_5finj
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_seq_unit_inj x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_symm.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_symm.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsymm
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_symm.case_0
  store_step with ih.eo__24mk_5fsymm s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_prog_symm.case_0 using

/-- logos's `__eo_prog_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsymm.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_symm x_a0 =
      (firstSome [EoCases.__eo_prog_symm.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_symm
  unfold EoCases.__eo_prog_symm.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_symm x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsymm.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsymm
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fsymm_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_symm.case_0

theorem eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsymm.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsymm s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_symm x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsymm_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_trans.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_trans.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrans
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_trans.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_and.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_trans.case_0
  store_step with ih.eo__24mk_5ftrans s2 v14 v11 v4 _ _ _ hinv2 h64 (hG.rem hrem) h_v14 h_v11 h_v4 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  case_done hinv3 hG with h_v16 in EoCases.__eo_prog_trans.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_trans` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrans.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_trans x_a0 =
      (firstSome [EoCases.__eo_prog_trans.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_trans
  unfold EoCases.__eo_prog_trans.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trans x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrans.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrans
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrans_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_trans.case_0

theorem eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrans.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ftrans
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrans s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_trans x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrans_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrue_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ftrue_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_true_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_true_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrue_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_true_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_true_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_true_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_true_elim.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_true_elim.case_0
  case_done hinv2 hG with h_v7 in EoCases.__eo_prog_true_elim.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_true_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrue_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_true_elim x_a0 =
      (firstSome [EoCases.__eo_prog_true_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_true_elim
  unfold EoCases.__eo_prog_true_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrue_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ftrue_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_true_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrue_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrue_5felim
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrue_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_true_elim.case_0

theorem eo__24eo_5fprog_5ftrue_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrue_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ftrue_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrue_5felim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_true_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrue_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrue_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : ProofOK x_a0) :
    case_0_eo__24eo_5fprog_5ftrue_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_true_intro.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_true_intro.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrue_5fintro
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_true_intro.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  have hn_v1 := hg_a0 _ rfl
  store_step with Store.apply_rep s1 v2 v1 _ _ hinv1 h64 h_v2 h_v1 (by ns_tac) (by ns_tac) as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s3 v3 v4 _ _ hinv3 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v5 in EoCases.__eo_prog_true_intro.case_0 using hn_v1

/-- logos's `__eo_prog_true_intro` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrue_5fintro.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_true_intro x_a0 =
      (firstSome [EoCases.__eo_prog_true_intro.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_true_intro
  unfold EoCases.__eo_prog_true_intro.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrue_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : ProofOK x_a0) :
    body_eo__24eo_5fprog_5ftrue_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_true_intro x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrue_5fintro.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrue_5fintro
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrue_5fintro_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_true_intro.case_0

theorem eo__24eo_5fprog_5ftrue_5fintro_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrue_5fintro.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fprog_5ftrue_5fintro
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrue_5fintro s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_true_intro x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrue_5fintro_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrust_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5ftrust s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_trust.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_trust.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrust
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_trust.case_0
  case_done hinv hG with h_a0 in EoCases.__eo_prog_trust.case_0 using hn_a0

/-- logos's `__eo_prog_trust` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrust.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_trust x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_trust.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_trust
  unfold EoCases.__eo_prog_trust.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrust_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5ftrust s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trust x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrust.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5ftrust
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5ftrust_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_trust.case_0

theorem eo__24eo_5fprog_5ftrust_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrust.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5ftrust
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrust s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_trust x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrust_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3e_3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v14 v16 _ _ hinv6 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v17 a1 _ _ hinv7 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v13 v18 _ _ hinv8 h64 h_v13 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v20 (by rw [he_v20]; exact empty_args) hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3e_3d.construct s10 e_v21 (by rw [he_v21]; exact empty_args) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v21 a1 _ _ hinv11 h64 h_v21 h_a1 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_int_2epow2.construct s12 e_v23 (by rw [he_v23]; exact empty_args) hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s13 v23 a2 _ _ hinv13 h64 h_v23 h_a2 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s14 v22 v24 _ _ hinv14 h64 h_v22 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s15 v20 v25 _ _ hinv15 h64 h_v20 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.literal_boolean_spec s16 false hinv16 h64 as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s17 v26 v27 _ _ hinv17 h64 h_v26 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_ite.construct s18 e_v29 (by rw [he_v29]; exact empty_args) hinv18 h64 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3c.construct s19 e_v30 (by rw [he_v30]; exact empty_args) hinv19 h64 as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s20 v30 a1 _ _ hinv20 h64 h_v30 h_a1 (by ns_tac) (by ns_tac) as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s21 0#u32 (0) (by scalar_tac) hinv21 h64 as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s22 v31 v32 _ _ hinv22 h64 h_v31 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s23, hinv23, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s23 v29 v33 _ _ hinv23 h64 h_v29 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s24, hinv24, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.literal_boolean_spec s24 true hinv24 h64 as ⟨v35, s25, hinv25, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s25 v34 v35 _ _ hinv25 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s26, hinv26, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_bvuge.construct s26 e_v37 (by rw [he_v37]; exact empty_args) hinv26 h64 as ⟨v37, s27, hinv27, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s27 v37 a0 _ _ hinv27 h64 h_v37 h_a0 (by ns_tac) (by ns_tac) as ⟨v38, s28, hinv28, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s28 e_v39 (by rw [he_v39]; rfl) h_a2 hinv28 h64 as ⟨v39, s29, hinv29, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s29 v39 a1 _ _ hinv29 h64 h_v39 h_a1 (by ns_tac) (by ns_tac) as ⟨v40, s30, hinv30, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s30 v38 v40 _ _ hinv30 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s31, hinv31, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s31 v36 v41 _ _ hinv31 h64 h_v36 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s32, hinv32, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s32 v28 v42 _ _ hinv32 h64 h_v28 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s33, hinv33, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s33 v19 v43 _ _ hinv33 h64 h_v19 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s34, hinv34, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  case_done hinv34 hG with h_v44 in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_uf_bv2nat_geq_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_geq_elim
  unfold EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_same v4 a0 with h_v4 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v14 (by rw [he_v14]; rfl) h_a0 hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v15 a1 _ _ hinv5 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v14 v16 _ _ hinv6 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v13 v17 _ _ hinv7 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v18 a1 _ _ hinv8 h64 h_v18 h_a1 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv9 hG with h_v19 in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_uf_bv2nat_int2bv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_int2bv
  unfold EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v35 a0 with h_v35 h_a0 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v39 a1 with h_v39 h_a1 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v41 (by rw [he_v41]; exact empty_args) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v42 (by rw [he_v42]; rfl) h_a0 hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v43 (by rw [he_v43]; exact empty_args) hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s10 v43 a1 _ _ hinv10 h64 h_v43 h_a1 (by ns_tac) (by ns_tac) as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s11 v42 v44 _ _ hinv11 h64 h_v42 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s12 v41 v45 _ _ hinv12 h64 h_v41 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_concat.construct s13 e_v47 (by rw [he_v47]; exact empty_args) hinv13 h64 as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v48 (by rw [he_v48]; rfl) h_a2 hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 0#u32 (0) (by scalar_tac) hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s16 v48 v49 _ _ hinv16 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s17 v47 v50 _ _ hinv17 h64 h_v47 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo_concat.construct s18 e_v52 (by rw [he_v52]; exact empty_args) hinv18 h64 as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s19 v52 a1 _ _ hinv19 h64 h_v52 h_a1 (by ns_tac) (by ns_tac) as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s20 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv20 h64 as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s21 v53 v54 _ _ hinv21 h64 h_v53 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s22 v51 v55 _ _ hinv22 h64 h_v51 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s23 v46 v56 _ _ hinv23 h64 h_v46 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  case_done hinv24 hG with h_v57 in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39

/-- logos's `__eo_prog_uf_bv2nat_int2bv_extend` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_int2bv_extend
  unfold EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v35 a0 with h_v35 h_a0 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36
  pat_same v32 v37 with h_v32 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v38 (by rw [he_v38]; exact empty_args) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v39 (by rw [he_v39]; rfl) h_a0 hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v40 (by rw [he_v40]; exact empty_args) hinv9 h64 as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s10 v40 a1 _ _ hinv10 h64 h_v40 h_a1 (by ns_tac) (by ns_tac) as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s11 v39 v41 _ _ hinv11 h64 h_v39 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s12 v38 v42 _ _ hinv12 h64 h_v38 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 0#u32 (0) (by scalar_tac) hinv13 h64 as ⟨v44, s14, hinv14, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_extract.construct s14 e_v45 (by rw [he_v45]; rfl) h_a2 h_v44 hinv14 h64 as ⟨v45, s15, hinv15, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s15 v45 a1 _ _ hinv15 h64 h_v45 h_a1 (by ns_tac) (by ns_tac) as ⟨v46, s16, hinv16, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s16 v43 v46 _ _ hinv16 h64 h_v43 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s17, hinv17, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  case_done hinv17 hG with h_v47 in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35

/-- logos's `__eo_prog_uf_bv2nat_int2bv_extract` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_int2bv_extract
  unfold EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s2 e_v2 (by rw [he_v2]; rfl) h_a0 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_int_2epow2.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_uf_int2bv_bv2nat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_uf_int2bv_bv2nat x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_int2bv_bv2nat
  unfold EoCases.__eo_prog_uf_int2bv_bv2nat.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bv2nat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_int2bv_bv2nat.case_0

theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_uf_int2bv_bv2nat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvule.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3c_3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_uf_int2bv_bvule_equiv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_int2bv_bvule_equiv
  unfold EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0

theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvult.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3c.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_uf_int2bv_bvult_equiv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_int2bv_bvult_equiv
  unfold EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0

theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_1_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_2_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_3_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_int_2epow2.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v36 a0 with h_v36 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v38 (by rw [he_v38]; exact empty_args) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_sbv_5fto_5fint.construct s8 e_v39 (by rw [he_v39]; exact empty_args) hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s9 v39 a0 _ _ hinv9 h64 h_v39 h_a0 (by ns_tac) (by ns_tac) as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s10 v38 v40 _ _ hinv10 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_ite.construct s11 e_v42 (by rw [he_v42]; exact empty_args) hinv11 h64 as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v43 (by rw [he_v43]; exact empty_args) hinv12 h64 as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_extract.construct s13 e_v44 (by rw [he_v44]; rfl) h_a1 h_a1 hinv13 h64 as ⟨v44, s14, hinv14, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s14 v44 a0 _ _ hinv14 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s15, hinv15, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s15 v43 v45 _ _ hinv15 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s16, hinv16, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 1#u32 (1) (by scalar_tac) hinv16 h64 as ⟨v47, s17, hinv17, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s17 e_v48 (by rw [he_v48]; rfl) h_v47 hinv17 h64 as ⟨v48, s18, hinv18, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v49, s19, hinv19, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s19 v48 v49 _ _ hinv19 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s20, hinv20, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s20 v46 v50 _ _ hinv20 h64 h_v46 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s21, hinv21, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s21 v42 v51 _ _ hinv21 h64 h_v42 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s22, hinv22, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s22 e_v53 (by rw [he_v53]; exact empty_args) hinv22 h64 as ⟨v53, s23, hinv23, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s23 v53 a0 _ _ hinv23 h64 h_v53 h_a0 (by ns_tac) (by ns_tac) as ⟨v54, s24, hinv24, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s24 v52 v54 _ _ hinv24 h64 h_v52 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s25, hinv25, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__2d.construct s25 e_v56 (by rw [he_v56]; exact empty_args) hinv25 h64 as ⟨v56, s26, hinv26, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s26 e_v57 (by rw [he_v57]; exact empty_args) hinv26 h64 as ⟨v57, s27, hinv27, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.apply_rep s27 v57 a0 _ _ hinv27 h64 h_v57 h_a0 (by ns_tac) (by ns_tac) as ⟨v58, s28, hinv28, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s28 v56 v58 _ _ hinv28 h64 h_v56 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s29, hinv29, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  store_step with Store.apply_rep s29 v59 a2 _ _ hinv29 h64 h_v59 h_a2 (by ns_tac) (by ns_tac) as ⟨v60, s30, hinv30, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s30 v55 v60 _ _ hinv30 h64 h_v55 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s31, hinv31, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  store_step with Store.apply_rep s31 v41 v61 _ _ hinv31 h64 h_v41 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s32, hinv32, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  case_done hinv32 hG with h_v62 in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v35 hn_v36

/-- logos's `__eo_prog_uf_sbv_to_int_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_sbv_to_int_elim
  unfold EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0

theorem eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_xor_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_xor_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fxor_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_xor_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_xor.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_xor_elim1.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s2 v9 v7 _ _ hinv2 h64 h_v9 h_v7 (by ns_tac) (by ns_tac) as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s4 v11 v4 _ _ hinv4 h64 h_v11 h_v4 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s6 v12 v13 _ _ hinv6 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s7 v10 v14 _ _ hinv7 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv8 hG with h_v15 in EoCases.__eo_prog_xor_elim1.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_xor_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fxor_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_xor_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_xor_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_xor_elim1
  unfold EoCases.__eo_prog_xor_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_xor_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fxor_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fxor_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fxor_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_xor_elim1.case_0

theorem eo__24eo_5fprog_5fxor_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fxor_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fxor_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fxor_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_xor_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fxor_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_xor_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_xor_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fxor_5felim2 more_0_eo__24eo_5fprog_5fxor_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_xor_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_xor.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_xor_elim2.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s3 v10 v7 _ _ hinv3 h64 h_v10 h_v7 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s4 v9 v11 _ _ hinv4 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s6 e_v14 (by rw [he_v14]; exact empty_args) hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s7 v14 v4 _ _ hinv7 h64 h_v14 h_v4 (by ns_tac) (by ns_tac) as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s8 v13 v15 _ _ hinv8 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.literal_boolean_spec s9 false hinv9 h64 as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s10 v16 v17 _ _ hinv10 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s11, hinv11, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s11 v12 v18 _ _ hinv11 h64 h_v12 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s12, hinv12, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv12 hG with h_v19 in EoCases.__eo_prog_xor_elim2.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_xor_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fxor_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_xor_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_xor_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_xor_elim2
  unfold EoCases.__eo_prog_xor_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_xor_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fxor_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fxor_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fxor_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_xor_elim2.case_0

theorem eo__24eo_5fprog_5fxor_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fxor_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fxor_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fxor_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_xor_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fxor_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_assume_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eassume_5fpush.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_assume_check.case_0 using

theorem case_1_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_assume_check.case_1 using

/-- logos's `__eo_push_assume_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fassume_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_assume_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_assume_check
  unfold EoCases.__eo_push_assume_check.case_0 EoCases.__eo_push_assume_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fassume_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fassume_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5fassume_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_assume_check.case_0 EoCases.__eo_push_assume_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fassume_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5fassume_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fassume_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fassume_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_input_assume_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eassume.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_input_assume_check.case_0 using

theorem case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_input_assume_check.case_1 using

/-- logos's `__eo_push_input_assume_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5finput_5fassume_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_input_assume_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_input_assume_check
  unfold EoCases.__eo_push_input_assume_check.case_0 EoCases.__eo_push_input_assume_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5finput_5fassume_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_input_assume_check.case_0 EoCases.__eo_push_input_assume_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5finput_5fassume_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5finput_5fassume_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_proven_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eproven.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_proven_check.case_0 using

theorem case_1_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_proven_check.case_1 using

/-- logos's `__eo_push_proven_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fproven_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_proven_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_proven_check
  unfold EoCases.__eo_push_proven_check.case_0 EoCases.__eo_push_proven_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fproven_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fproven_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5fproven_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_proven_check.case_0 EoCases.__eo_push_proven_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fproven_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5fproven_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fproven_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fproven_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_0 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_state_is_closed.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_state_is_closed.case_0
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  case_done hinv1 hG with h_v5 in EoCases.__eo_state_is_closed.case_0 using

theorem case_1_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_1 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_state_is_closed.case_1
  case_again hinv hG with h_v2 goods 1 in EoCases.__eo_state_is_closed.case_1 using

theorem case_2_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_2_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_2 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_state_is_closed.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_state_is_closed.case_2 using

theorem case_3_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_3_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_3 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_state_is_closed.case_3 using

/-- logos's `__eo_state_is_closed` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fstate_5fis_5fclosed.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_state_is_closed x_a0 =
      (firstSome [EoCases.__eo_state_is_closed.case_0 x_a0, EoCases.__eo_state_is_closed.case_1 x_a0, EoCases.__eo_state_is_closed.case_2 x_a0, EoCases.__eo_state_is_closed.case_3 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_state_is_closed
  unfold EoCases.__eo_state_is_closed.case_0 EoCases.__eo_state_is_closed.case_1 EoCases.__eo_state_is_closed.case_2 EoCases.__eo_state_is_closed.case_3
  logos_eq

theorem step_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    step_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          __eo_state_is_closed x_a0 = __eo_state_is_closed y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fstate_5fis_5fclosed.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  round_step with case_0_eo__24eo_5fstate_5fis_5fclosed_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using
  round_step with case_1_eo__24eo_5fstate_5fis_5fclosed_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hc0
  round_step with case_2_eo__24eo_5fstate_5fis_5fclosed_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hc0 hc1
  round_step with case_3_eo__24eo_5fstate_5fis_5fclosed_spec n ih s4 a0 x_a0 hinv4 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__eo_state_is_closed.case_0 EoCases.__eo_state_is_closed.case_1 EoCases.__eo_state_is_closed.case_2 EoCases.__eo_state_is_closed.case_3 splitting x_a0

theorem body_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → StateOK x_a0 →
      body_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0 hg_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0 hg_a0
  unfold body_eo__24eo_5fstate_5fis_5fclosed body_eo__24eo_5fstate_5fis_5fclosed_loop
  step with step_eo__24eo_5fstate_5fis_5fclosed_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, hnext, hrep0, hgood0, heq⟩ := hr
      simp only
      have hlen : next.length = 1 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      have hrec := ihl s1.budget (by omega) b0 s1 y0 le_rfl hinv1 (hg1.rem hrem)  hrep0  hgood0
      unfold body_eo__24eo_5fstate_5fis_5fclosed at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fis_5fclosed.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fstate_5fis_5fclosed
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fstate_5fis_5fclosed s1 a0) (fun s' t => Represents.rep s' t (__eo_state_is_closed x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fstate_5fis_5fclosed_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_state_is_refutation.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_state_is_refutation.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fstate_5fis_5frefutation
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 (by good_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with ih.eo__24eo_5fstate_5fis_5fclosed s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 (by good_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_state_is_refutation.case_0 using

/-- logos's `__eo_state_is_refutation` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fstate_5fis_5frefutation.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_state_is_refutation x_a0 =
      (firstSome [EoCases.__eo_state_is_refutation.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_state_is_refutation
  unfold EoCases.__eo_state_is_refutation.case_0
  logos_eq

theorem body_eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_refutation x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fstate_5fis_5frefutation.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fstate_5fis_5frefutation
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fstate_5fis_5frefutation_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_state_is_refutation.case_0 splitting x_a0

theorem eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fis_5frefutation.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fstate_5fis_5frefutation
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fstate_5fis_5frefutation s1 a0) (fun s' t => Represents.rep s' t (__eo_state_is_refutation x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fstate_5fis_5frefutation_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- `$eo_state_proven_nth`, by the proof written by hand. -/
theorem eo__24eo_5fstate_5fproven_5fnth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fproven_5fnth.Spec n :=
  state_proven_nth_spec n (fun m hm => (ih m hm).eo__24eo_5fStateObj_5fproven)

theorem case_0_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_0_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_array_deq_diff.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_array_deq_diff.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_array_deq_diff.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a3 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__eo_to_smt_array_deq_diff.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emap_5fdiff.construct s e_v6 (by rw [he_v6]; rfl) h_a0 h_a2 hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v2 h_v4 h_v5
  case_done hinv1 hG with h_v6 in EoCases.__eo_to_smt_array_deq_diff.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_1_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_array_deq_diff.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_array_deq_diff.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_array_deq_diff.case_1 using

/-- logos's `__eo_to_smt_array_deq_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_to_smt_array_deq_diff x_a0 x_a1 x_a2 x_a3 =
      (firstSome [EoCases.__eo_to_smt_array_deq_diff.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_to_smt_array_deq_diff.case_1 x_a0 x_a1 x_a2 x_a3] default) := by
  conv => lhs; unfold __eo_to_smt_array_deq_diff
  unfold EoCases.__eo_to_smt_array_deq_diff.case_0 EoCases.__eo_to_smt_array_deq_diff.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_array_deq_diff x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_array_deq_diff.case_0 EoCases.__eo_to_smt_array_deq_diff.case_1 splitting x_a0 x_a1 x_a2 x_a3

theorem eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_to_smt_array_deq_diff x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5farray_5fdeq_5fdiff_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fbv_5fsize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fbv_5fsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_bv_size.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_bv_size.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fbv_5fsize
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_bv_size.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_nat_to_int s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  rw [← Bridge.native_nat_to_int] at h_v2
  case_done hinv1 hG with h_v2 in EoCases.__eo_to_smt_bv_size.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fbv_5fsize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fbv_5fsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_bv_size.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_bv_size.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fbv_5fsize
  have hG := Store.Grows.refl s
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 1#u32 (1) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_zneg s1 e_v1 (by rw [he_v1]; rfl) h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  rw [← Bridge.native_zneg] at h_v1
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_bv_size.case_1 using

/-- logos's `__eo_to_smt_bv_size` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fbv_5fsize.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_bv_size x_a0 =
      (firstSome [EoCases.__eo_to_smt_bv_size.case_0 x_a0, EoCases.__eo_to_smt_bv_size.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_bv_size
  unfold EoCases.__eo_to_smt_bv_size.case_0 EoCases.__eo_to_smt_bv_size.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fbv_5fsize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fbv_5fsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_bv_size x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fbv_5fsize.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fbv_5fsize
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fbv_5fsize_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fbv_5fsize_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_bv_size.case_0 EoCases.__eo_to_smt_bv_size.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fbv_5fsize_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fbv_5fsize.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fbv_5fsize
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fbv_5fsize s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_bv_size x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fbv_5fsize_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fdatatype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_datatype.case_0
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fcons s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt_datatype.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fdatatype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_datatype.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_datatype.case_1 using

/-- logos's `__eo_to_smt_datatype` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fdatatype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_datatype x_a0 =
      (firstSome [EoCases.__eo_to_smt_datatype.case_0 x_a0, EoCases.__eo_to_smt_datatype.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_datatype
  unfold EoCases.__eo_to_smt_datatype.case_0 EoCases.__eo_to_smt_datatype.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fdatatype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fdatatype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fdatatype
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fdatatype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fdatatype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_datatype.case_0 EoCases.__eo_to_smt_datatype.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fdatatype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fdatatype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fdatatype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 749#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fdatatype s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_datatype x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_749 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_749 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fdatatype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_cons.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_cons.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_datatype_cons.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_datatype_cons.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_cons.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_cons.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_datatype_cons.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fcons s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_to_smt_datatype_cons.case_1 using

/-- logos's `__eo_to_smt_datatype_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fdatatype_5fcons.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_datatype_cons x_a0 =
      (firstSome [EoCases.__eo_to_smt_datatype_cons.case_0 x_a0, EoCases.__eo_to_smt_datatype_cons.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_datatype_cons
  unfold EoCases.__eo_to_smt_datatype_cons.case_0 EoCases.__eo_to_smt_datatype_cons.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype_cons x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fdatatype_5fcons.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_datatype_cons.case_0 EoCases.__eo_to_smt_datatype_cons.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fdatatype_5fcons.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fdatatype_5fcons
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 750#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_datatype_cons x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_750 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_750 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
