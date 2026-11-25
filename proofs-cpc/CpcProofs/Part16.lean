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

theorem case_0_eo__24get_5fnth_5fvar_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24get_5fnth_5fvar_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__get_nth_var_type.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__get_nth_var_type.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24get_5fnth_5fvar_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__get_nth_var_type.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__get_nth_var_type.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s1 e_v7 (by rw [he_v7]; rfl) h_v6 h_v5 h_a1 hinv1 h64 (hG.rem hrem) (by not_left_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24get_5fvar_5ftype s2 v7 _ hinv2 h64 (hG.rem hrem) h_v7 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  case_done hinv3 hG with h_v8 in EoCases.__get_nth_var_type.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__get_nth_var_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24get_5fnth_5fvar_5ftype.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __get_nth_var_type x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__get_nth_var_type.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __get_nth_var_type
  unfold EoCases.__get_nth_var_type.case_0
  logos_eq

theorem body_eo__24get_5fnth_5fvar_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24get_5fnth_5fvar_5ftype s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_nth_var_type x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24get_5fnth_5fvar_5ftype.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24get_5fnth_5fvar_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24get_5fnth_5fvar_5ftype_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__get_nth_var_type.case_0

theorem eo__24get_5fnth_5fvar_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24get_5fnth_5fvar_5ftype.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24get_5fnth_5fvar_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 894#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24get_5fnth_5fvar_5ftype s1 a0 a1) (fun s' t => Represents.rep s' t (__get_nth_var_type x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_894 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_894 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24get_5fnth_5fvar_5ftype_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24get_5fvar_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24get_5fvar_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__get_var_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__get_var_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24get_5fvar_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__get_var_type.case_0
  case_done hinv hG with h_v2 in EoCases.__get_var_type.case_0 using hn_a0

/-- logos's `__get_var_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24get_5fvar_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __get_var_type x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__get_var_type.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __get_var_type
  unfold EoCases.__get_var_type.case_0
  logos_eq

theorem body_eo__24get_5fvar_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24get_5fvar_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__get_var_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24get_5fvar_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24get_5fvar_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24get_5fvar_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__get_var_type.case_0

theorem eo__24get_5fvar_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24get_5fvar_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24get_5fvar_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24get_5fvar_5ftype s1 a0) (fun s' t => Represents.rep s' t (__get_var_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24get_5fvar_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24greatest_5fint_5flt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24greatest_5fint_5flt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__greatest_int_lt.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__greatest_int_lt.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24greatest_5fint_5flt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_q s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_to_z s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_to_q s2 e_v2 (by rw [he_v2]; rfl) h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_eq s3 e_v3 (by rw [he_v3]; rfl) h_v0 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  have h_ite_v8 := (show if_0_eo__24greatest_5fint_5flt s4 v3 a0 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24greatest_5fint_5flt
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
      step as ⟨e_v5, he_v5⟩
      store_step with Store.builtin_spec_to_z s5 e_v5 (by rw [he_v5]; rfl) h_a0 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
      step as ⟨e_v6, he_v6⟩
      store_step with Store.builtin_spec_add s6 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
      ite_done hinv7 hG with (eo_ite_true_rep _ hx_4 h_v6)
    · ite_branch hbv_4
      step as ⟨e_v7, he_v7⟩
      store_step with Store.builtin_spec_to_z s4 e_v7 (by rw [he_v7]; rfl) h_a0 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_4 h_v7)
    · ite_branch hbv_4
      ite_stuck hinv4 hG with hx_4)
  store_step with h_ite_v8 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v8 in EoCases.__greatest_int_lt.case_0 using hn_a0

/-- logos's `__greatest_int_lt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24greatest_5fint_5flt.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __greatest_int_lt x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__greatest_int_lt.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __greatest_int_lt
  unfold EoCases.__greatest_int_lt.case_0
  logos_eq

theorem body_eo__24greatest_5fint_5flt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24greatest_5fint_5flt s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__greatest_int_lt x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24greatest_5fint_5flt.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24greatest_5fint_5flt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24greatest_5fint_5flt_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__greatest_int_lt.case_0

theorem eo__24greatest_5fint_5flt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24greatest_5fint_5flt.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24greatest_5fint_5flt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24greatest_5fint_5flt s1 a0) (fun s' t => Represents.rep s' t (__greatest_int_lt x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24greatest_5fint_5flt_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24iota_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24iota_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__iota_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__iota_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24iota_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__iota_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__iota_rec.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__iota_rec.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Int.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s4 v5 v6 _ _ hinv4 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v7 in EoCases.__iota_rec.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24iota_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24iota_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__iota_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__iota_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24iota_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__iota_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__iota_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__iota_rec.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__iota_rec.case_1
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a1 _ _ hinv3 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_add s5 e_v11 (by rw [he_v11]; rfl) h_a1 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24iota_5frec s6 v2 v11 _ _ hinv6 h64 (hG.rem hrem) h_v2 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_mk_rep s7 v9 v12 _ _ hinv7 h64 h_v9 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v13 in EoCases.__iota_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__iota_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24iota_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __iota_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__iota_rec.case_0 x_a0 x_a1, EoCases.__iota_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __iota_rec
  unfold EoCases.__iota_rec.case_0 EoCases.__iota_rec.case_1
  logos_eq

theorem body_eo__24iota_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24iota_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__iota_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24iota_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24iota_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24iota_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24iota_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__iota_rec.case_0 EoCases.__iota_rec.case_1

theorem eo__24iota_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24iota_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24iota_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 899#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24iota_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__iota_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_899 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_899 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24iota_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24is_5farith_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5farith_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_arith_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_arith_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5farith_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__is_arith_type.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__is_arith_type.case_0 using hn_a0

theorem case_1_eo__24is_5farith_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5farith_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_arith_type.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_arith_type.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5farith_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__is_arith_type.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__is_arith_type.case_1 using hn_a0

/-- logos's `__is_arith_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5farith_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __is_arith_type x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_arith_type.case_0 x_a0, EoCases.__is_arith_type.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __is_arith_type
  unfold EoCases.__is_arith_type.case_0 EoCases.__is_arith_type.case_1
  logos_eq

theorem body_eo__24is_5farith_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24is_5farith_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_arith_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5farith_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24is_5farith_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24is_5farith_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24is_5farith_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__is_arith_type.case_0 EoCases.__is_arith_type.case_1

theorem eo__24is_5farith_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5farith_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24is_5farith_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24is_5farith_5ftype s1 a0) (fun s' t => Represents.rep s' t (__is_arith_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5farith_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
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
  unfold case_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts more_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_poly_norm_rel_consts.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_to_q s e_v6 (by rw [he_v6]; rfl) h_v5 hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  replace h_v8 := Represents.rep_of_eq h_v8 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_eq s2 e_v9 (by rw [he_v9]; rfl) h_v6 h_v8 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_to_q s3 e_v10 (by rw [he_v10]; rfl) h_v2 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s4 _ hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10
  replace h_v12 := Represents.rep_of_eq h_v12 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v13, he_v13⟩
  store_step with Store.builtin_spec_eq s5 e_v13 (by rw [he_v13]; rfl) h_v10 h_v12 hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_or s6 e_v14 (by rw [he_v14]; rfl) h_v9 h_v13 hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_not s7 e_v15 (by rw [he_v15]; rfl) h_v14 hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s8 v4 v5 _ _ hinv8 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s9 v16 v2 _ _ hinv9 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with ih.eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s10 v17 _ hinv10 h64 (hG.rem hrem) h_v17 as ⟨v18, s11, hinv11, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with Store.builtin_spec_and s11 e_v19 (by rw [he_v19]; rfl) h_v15 h_v18 hinv11 h64 as ⟨v19, s12, hinv12, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
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
  store_step with CtorSpec.eo__3c.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  have h_ite_v14 := (show if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9
      have h_ite_v13 := (show if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14
  have h_ite_v22 := (show if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_3_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17
      have h_ite_v21 := (show if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v22
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
  store_step with CtorSpec.eo__3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  have h_ite_v14 := (show if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_5_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9
      have h_ite_v13 := (show if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_4_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14
  have h_ite_v22 := (show if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_7_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17
      have h_ite_v21 := (show if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_6_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v22
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
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_2
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
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
  store_step with CtorSpec.eo__3e_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_3
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  have h_ite_v14 := (show if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_9_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9
      have h_ite_v13 := (show if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_8_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14
  have h_ite_v22 := (show if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_11_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17
      have h_ite_v21 := (show if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_10_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v22
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
  store_step with CtorSpec.eo__3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_poly_norm_rel_consts_rel.case_4
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_is_neg s1 e_v7 (by rw [he_v7]; rfl) h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  have h_ite_v14 := (show if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s2 v7 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_13_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s2 1#u32 (-1) (by scalar_tac) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.builtin_spec_neg s2 e_v9 (by rw [he_v9]; rfl) h_v5 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_is_neg s3 e_v10 (by rw [he_v10]; rfl) h_v9 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9
      have h_ite_v13 := (show if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v10 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_12_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_true_rep _ hx_11 h_v11)
        · ite_branch hbv_11
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_11 h_v12)
        · ite_branch hbv_11
          ite_stuck hinv4 hG with hx_11)
      store_step with h_ite_v13 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
      ite_done hinv5 hG with (eo_ite_false_rep _ hx_8 h_v13)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v14 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_is_neg s3 e_v15 (by rw [he_v15]; rfl) h_v2 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14
  have h_ite_v22 := (show if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s4 v15 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_15_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_neg s4 e_v17 (by rw [he_v17]; rfl) h_v2 hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
      step as ⟨e_v18, he_v18⟩
      store_step with Store.builtin_spec_is_neg s5 e_v18 (by rw [he_v18]; rfl) h_v17 hinv5 h64 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17
      have h_ite_v21 := (show if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel s6 v18 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_14_eo__24is_5fpoly_5fnorm_5frel_5fconsts_5frel
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s6
        rcases Store.boolean_value_term h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_19 h_v19)
        · ite_branch hbv_19
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v20)
        · ite_branch hbv_19
          ite_stuck hinv6 hG with hx_19)
      store_step with h_ite_v21 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v17 h_v18
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_16 h_v21)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v22 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_eq s5 e_v23 (by rw [he_v23]; rfl) h_v14 h_v22 hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v14 h_v15 h_v22
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
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
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
  store_step with CtorSpec.eo_seq_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__is_seq_const.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
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
  store_step with ih.eo__24is_5fseq_5fconst_5frec s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
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
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_seq_const_rec.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_seq_const_rec.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9
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
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__is_seq_const_rec.case_1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_Seq.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__is_seq_const_rec.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__is_seq_const_rec.case_1 using hn_a0 hn_v3 hn_v4

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
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
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
  store_step with Store.literal_int_u32_spec s 1#u32 (1) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_to_z s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_add s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
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
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__lower_not_and.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
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
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__lower_not_and.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24lower_5fnot_5fand s5 v2 _ hinv5 h64 (hG.rem hrem) h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
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
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
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
  unfold case_1_eo__24mk_5farith_5fsum_5fub_5frec more_0_eo__24mk_5farith_5fsum_5fub_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_arith_sum_ub_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_a1 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv1 else hinv1 hG in EoCases.__mk_arith_sum_ub_rec.case_1
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v19 (by rw [he_v19]; exact empty_args) hinv1 h64 as ⟨v19, s2, hinv2, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18
  store_step with Store.apply_rep s2 v19 v12 _ _ hinv2 h64 h_v19 h_v12 (by ns_tac) (by ns_tac) as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s3 v20 v18 _ _ hinv3 h64 h_v20 h_v18 (by ns_tac) (by ns_tac) as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s4 e_v22 (by rw [he_v22]; exact empty_args) hinv4 h64 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s5 v22 v9 _ _ hinv5 h64 h_v22 h_v9 (by ns_tac) (by ns_tac) as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s6 v23 v15 _ _ hinv6 h64 h_v23 h_v15 (by ns_tac) (by ns_tac) as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with ih.eo__24arith_5frel_5fsum s7 v11 v17 v21 v24 _ _ _ _ hinv7 h64 (hG.rem hrem) h_v11 h_v17 h_v21 h_v24 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
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
  store_step with ih.eo__24arith_5frel_5ftrichotomy s v4 v10 v5 v2 _ _ _ _ hinv h64 hrem h_v4 h_v10 h_v5 h_v2 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
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
  store_step with CtorSpec.eo_and.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v16 (by rw [he_v16]; exact empty_args) hinv1 h64 as ⟨v16, s2, hinv2, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15
  pat_same v14 v16 with h_v14 h_v16 using hinv2 else hinv2 hG in EoCases.__mk_cong_rhs.case_0
  pat_same v15 v2 with h_v15 h_v2 using hinv2 else hinv2 hG in EoCases.__mk_cong_rhs.case_0
  store_step with ih.eo__24mk_5fcong_5frhs s2 v1 v5 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v5 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v16
  store_step with Store.apply_mk_rep s3 v17 v12 _ _ hinv3 h64 h_v17 h_v12 as ⟨v18, s4, hinv4, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v11 h_v12 h_v14 h_v15 h_v16 h_v17
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
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_cong_rhs.case_1
  case_done hinv1 hG with h_a0 in EoCases.__mk_cong_rhs.case_1 using hn_a0 hn_a1

/-- logos's `__mk_cong_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fcong_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_cong_rhs x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_cong_rhs.case_0 x_a0 x_a1, EoCases.__mk_cong_rhs.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_cong_rhs
  unfold EoCases.__mk_cong_rhs.case_0 EoCases.__mk_cong_rhs.case_1
  try unfold Eo.__eo_l_1___mk_cong_rhs
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
  store_step with CtorSpec.eo_distinct.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_0
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__mk_distinct_elim.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_distinct.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s3 v11 v6 _ _ hinv3 h64 h_v11 h_v6 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24mk_5fdistinct_5felim s4 v12 _ hinv4 h64 (hG.rem hrem) h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24mk_5fdistinct_5felim_5frec s5 v9 v6 v13 _ _ _ hinv5 h64 (hG.rem hrem) h_v9 h_v6 h_v13 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
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
  store_step with CtorSpec.eo_distinct.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
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
  unfold case_0_eo__24mk_5fdistinct_5felim_5frec more_0_eo__24mk_5fdistinct_5felim_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim_rec.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_distinct_elim_rec.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_distinct_elim_rec.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 a0 _ _ hinv4 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s7 v7 v12 _ _ hinv7 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24mk_5fdistinct_5felim_5frec s8 a0 v2 a2 _ _ _ hinv8 h64 (hG.rem hrem) h_a0 h_v2 h_a2 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_mk_rep s9 v13 v14 _ _ hinv9 h64 h_v13 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
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
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
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

theorem case_0_eo__24mk_5fdt_5finst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5finst_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_dt_inst_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__mk_dt_inst_rec.case_0 x_a0 x_a1 x_a2 = some (__mk_dt_inst_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__mk_dt_inst_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5finst_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst_rec.case_0
  case_done hinv1 hG with h_a2 in EoCases.__mk_dt_inst_rec.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24mk_5fdt_5finst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5finst_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_dt_inst_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__mk_dt_inst_rec.case_1 x_a0 x_a1 x_a2 = some (__mk_dt_inst_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__mk_dt_inst_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5finst_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_inst_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_inst_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst_rec.case_1
  store_step with Store.apply_rep s1 v5 a1 _ _ hinv1 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 a2 v7 _ _ hinv2 h64 h_a2 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  case_again hinv3 hG with h_v2 h_a1 h_v8 in EoCases.__mk_dt_inst_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__mk_dt_inst_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5finst_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_dt_inst_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_inst_rec.case_0 x_a0 x_a1 x_a2, EoCases.__mk_dt_inst_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_inst_rec
  unfold EoCases.__mk_dt_inst_rec.case_0 EoCases.__mk_dt_inst_rec.case_1
  logos_eq

theorem step_eo__24mk_5fdt_5finst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24mk_5fdt_5finst_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__mk_dt_inst_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __mk_dt_inst_rec x_a0 x_a1 x_a2 = __mk_dt_inst_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5finst_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24mk_5fdt_5finst_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24mk_5fdt_5finst_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24mk_5fdt_5finst_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_dt_inst_rec.case_0 EoCases.__mk_dt_inst_rec.case_1

theorem body_eo__24mk_5fdt_5finst_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fdt_5finst_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24mk_5fdt_5finst_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24mk_5fdt_5finst_5frec body_eo__24mk_5fdt_5finst_5frec_loop
  step with step_eo__24mk_5fdt_5finst_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24mk_5fdt_5finst_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24mk_5fdt_5finst_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5finst_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fdt_5finst_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 933#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5fdt_5finst_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_dt_inst_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_933 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_933 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5finst_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdt_5finst_5ftuple_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5finst_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst_tuple.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst_tuple.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5finst_5ftuple
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_inst_tuple.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_inst_tuple.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst_tuple.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_Tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24mk_5fdt_5finst_5ftuple_5frec s5 v9 a1 v10 _ _ _ hinv5 h64 (hG.rem hrem) h_v9 h_a1 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv6 hG with h_v11 in EoCases.__mk_dt_inst_tuple.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fdt_5finst_5ftuple_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5finst_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst_tuple.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst_tuple.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5finst_5ftuple
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst_tuple.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__mk_dt_inst_tuple.case_1 using hn_a0 hn_a1

/-- logos's `__mk_dt_inst_tuple` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5finst_5ftuple.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_dt_inst_tuple x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_inst_tuple.case_0 x_a0 x_a1, EoCases.__mk_dt_inst_tuple.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_inst_tuple
  unfold EoCases.__mk_dt_inst_tuple.case_0 EoCases.__mk_dt_inst_tuple.case_1
  logos_eq

theorem body_eo__24mk_5fdt_5finst_5ftuple_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fdt_5finst_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_tuple x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5finst_5ftuple.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fdt_5finst_5ftuple
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fdt_5finst_5ftuple_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fdt_5finst_5ftuple_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_dt_inst_tuple.case_0 EoCases.__mk_dt_inst_tuple.case_1

theorem eo__24mk_5fdt_5finst_5ftuple_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5finst_5ftuple.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fdt_5finst_5ftuple
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fdt_5finst_5ftuple s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_dt_inst_tuple x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5finst_5ftuple_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdt_5finst_5ftuple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5finst_5ftuple_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst_tuple_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst_tuple_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5finst_5ftuple_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst_tuple_rec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__mk_dt_inst_tuple_rec.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24mk_5fdt_5finst_5ftuple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5finst_5ftuple_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_inst_tuple_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_inst_tuple_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5finst_5ftuple_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_inst_tuple_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_inst_tuple_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_dt_inst_tuple_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_tuple_2eselect.construct s2 e_v8 (by rw [he_v8]; rfl) h_a2 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a1 _ _ hinv3 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_add s6 e_v12 (by rw [he_v12]; rfl) h_a2 h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24mk_5fdt_5finst_5ftuple_5frec s7 v2 a1 v12 _ _ _ hinv7 h64 (hG.rem hrem) h_v2 h_a1 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_mk_rep s8 v10 v13 _ _ hinv8 h64 h_v10 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv9 hG with h_v14 in EoCases.__mk_dt_inst_tuple_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__mk_dt_inst_tuple_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5finst_5ftuple_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_dt_inst_tuple_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_inst_tuple_rec.case_0 x_a0 x_a1 x_a2, EoCases.__mk_dt_inst_tuple_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_inst_tuple_rec
  unfold EoCases.__mk_dt_inst_tuple_rec.case_0 EoCases.__mk_dt_inst_tuple_rec.case_1
  logos_eq

theorem body_eo__24mk_5fdt_5finst_5ftuple_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fdt_5finst_5ftuple_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_inst_tuple_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5finst_5ftuple_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5fdt_5finst_5ftuple_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5fdt_5finst_5ftuple_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5fdt_5finst_5ftuple_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_dt_inst_tuple_rec.case_0 EoCases.__mk_dt_inst_tuple_rec.case_1

theorem eo__24mk_5fdt_5finst_5ftuple_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5finst_5ftuple_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fdt_5finst_5ftuple_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 935#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5fdt_5finst_5ftuple_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_dt_inst_tuple_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_935 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_935 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5finst_5ftuple_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fdt_5fsplit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_split.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_split.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fdt_5fsplit
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_dt_split.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__mk_dt_split.case_0 using hn_a0 hn_a1

theorem case_1_eo__24mk_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fdt_5fsplit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_dt_split.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_dt_split.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fdt_5fsplit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_dt_split.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_dt_split.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_dt_split.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_is.construct s2 e_v8 (by rw [he_v8]; rfl) h_v5 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a1 _ _ hinv3 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24mk_5fdt_5fsplit s5 v2 a1 _ _ hinv5 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__mk_dt_split.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__mk_dt_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fdt_5fsplit.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_dt_split x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_dt_split.case_0 x_a0 x_a1, EoCases.__mk_dt_split.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_dt_split
  unfold EoCases.__mk_dt_split.case_0 EoCases.__mk_dt_split.case_1
  logos_eq

theorem body_eo__24mk_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fdt_5fsplit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_dt_split x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fdt_5fsplit.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fdt_5fsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fdt_5fsplit_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fdt_5fsplit_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_dt_split.case_0 EoCases.__mk_dt_split.case_1

theorem eo__24mk_5fdt_5fsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fdt_5fsplit.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fdt_5fsplit
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 936#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5fdt_5fsplit s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_dt_split x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_936 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_936 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fdt_5fsplit_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fho_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fho_5fcong s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_ho_cong.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__mk_ho_cong.case_0 x_a0 x_a1 x_a2 = some (__mk_ho_cong y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__mk_ho_cong.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fho_5fcong
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_ho_cong.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_ho_cong.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_ho_cong.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_ho_cong.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_ho_cong.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_ho_cong.case_0
  store_step with Store.apply_rep s2 a0 v12 _ _ hinv2 h64 h_a0 h_v12 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s3 a1 v9 _ _ hinv3 h64 h_a1 h_v9 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  case_again hinv4 hG with h_v14 h_v15 h_v2 in EoCases.__mk_ho_cong.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24mk_5fho_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fho_5fcong s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_ho_cong.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__mk_ho_cong.case_1 x_a0 x_a1 x_a2 = some (__mk_ho_cong y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__mk_ho_cong.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fho_5fcong
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_ho_cong.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__mk_ho_cong.case_1 using hn_a0 hn_a1 hn_a2

/-- logos's `__mk_ho_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fho_5fcong.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_ho_cong x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_ho_cong.case_0 x_a0 x_a1 x_a2, EoCases.__mk_ho_cong.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_ho_cong
  unfold EoCases.__mk_ho_cong.case_0 EoCases.__mk_ho_cong.case_1
  logos_eq

theorem step_eo__24mk_5fho_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24mk_5fho_5fcong s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__mk_ho_cong x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __mk_ho_cong x_a0 x_a1 x_a2 = __mk_ho_cong y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fho_5fcong.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24mk_5fho_5fcong
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24mk_5fho_5fcong_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24mk_5fho_5fcong_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_ho_cong.case_0 EoCases.__mk_ho_cong.case_1

theorem body_eo__24mk_5fho_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fho_5fcong s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_ho_cong x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24mk_5fho_5fcong s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_ho_cong x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24mk_5fho_5fcong body_eo__24mk_5fho_5fcong_loop
  step with step_eo__24mk_5fho_5fcong_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24mk_5fho_5fcong at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24mk_5fho_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fho_5fcong.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fho_5fcong
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 939#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5fho_5fcong s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_ho_cong x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_939 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_939 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fho_5fcong_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fnary_5fcong_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fnary_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_nary_cong_rhs.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_nary_cong_rhs.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fnary_5fcong_5frhs more_0_eo__24mk_5fnary_5fcong_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_nary_cong_rhs.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_nary_cong_rhs.case_0
  pat_unapply h_a1 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__mk_nary_cong_rhs.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__mk_nary_cong_rhs.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_and.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__mk_nary_cong_rhs.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__mk_nary_cong_rhs.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv1 else hinv1 hG in EoCases.__mk_nary_cong_rhs.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v19 (by rw [he_v19]; exact empty_args) hinv1 h64 as ⟨v19, s2, hinv2, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv2 else hinv2 hG in EoCases.__mk_nary_cong_rhs.case_0
  pat_same v18 v5 with h_v18 h_v5 using hinv2 else hinv2 hG in EoCases.__mk_nary_cong_rhs.case_0
  store_step with Store.apply_rep s2 v4 v15 _ _ hinv2 h64 h_v4 h_v15 (by ns_tac) (by ns_tac) as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19
  store_step with ih.eo__24mk_5fnary_5fcong_5frhs s3 v2 v8 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v8 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_mk_rep s4 v20 v21 _ _ hinv4 h64 h_v20 h_v21 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  case_done hinv5 hG with h_v22 in EoCases.__mk_nary_cong_rhs.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11 hn_v14 hn_v15 hn_v17 hn_v18

theorem case_1_eo__24mk_5fnary_5fcong_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fnary_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_nary_cong_rhs.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_nary_cong_rhs.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fnary_5fcong_5frhs
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_nary_cong_rhs.case_1
  case_done hinv1 hG with h_a0 in EoCases.__mk_nary_cong_rhs.case_1 using hn_a0 hn_a1

/-- logos's `__mk_nary_cong_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fnary_5fcong_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_nary_cong_rhs x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_nary_cong_rhs.case_0 x_a0 x_a1, EoCases.__mk_nary_cong_rhs.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_nary_cong_rhs
  unfold EoCases.__mk_nary_cong_rhs.case_0 EoCases.__mk_nary_cong_rhs.case_1
  try unfold Eo.__eo_l_1___mk_nary_cong_rhs
  logos_eq_deep

theorem body_eo__24mk_5fnary_5fcong_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fnary_5fcong_5frhs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_nary_cong_rhs x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fnary_5fcong_5frhs.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fnary_5fcong_5frhs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fnary_5fcong_5frhs_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fnary_5fcong_5frhs_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_nary_cong_rhs.case_0 EoCases.__mk_nary_cong_rhs.case_1

theorem eo__24mk_5fnary_5fcong_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fnary_5fcong_5frhs.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fnary_5fcong_5frhs
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 940#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5fnary_5fcong_5frhs s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_nary_cong_rhs x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_940 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_940 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fnary_5fcong_5frhs_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fquant_5fmerge_5fprenex_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fquant_5fmerge_5fprenex s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_quant_merge_prenex.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__mk_quant_merge_prenex.case_0 x_a0 x_a1 x_a2 = some (__mk_quant_merge_prenex y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__mk_quant_merge_prenex.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fquant_5fmerge_5fprenex
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_quant_merge_prenex.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_quant_merge_prenex.case_0
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__mk_quant_merge_prenex.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s1 e_v7 (by rw [he_v7]; rfl) h_v6 h_a2 h_v5 hinv1 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  case_again hinv2 hG with h_a0 h_v2 h_v7 in EoCases.__mk_quant_merge_prenex.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fquant_5fmerge_5fprenex_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fquant_5fmerge_5fprenex s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_quant_merge_prenex.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__mk_quant_merge_prenex.case_1 x_a0 x_a1 x_a2 = some (__mk_quant_merge_prenex y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__mk_quant_merge_prenex.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fquant_5fmerge_5fprenex
  have hG := Store.Grows.refl s
  store_step with Store.apply_rep s a0 a2 _ _ hinv h64 h_a0 h_a2 (by ns_tac) (by ns_tac) as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  store_step with Store.apply_rep s1 v0 a1 _ _ hinv1 h64 h_v0 h_a1 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__mk_quant_merge_prenex.case_1 using hn_a0 hn_a1 hn_a2

/-- logos's `__mk_quant_merge_prenex` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fquant_5fmerge_5fprenex.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_quant_merge_prenex x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_quant_merge_prenex.case_0 x_a0 x_a1 x_a2, EoCases.__mk_quant_merge_prenex.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_quant_merge_prenex
  unfold EoCases.__mk_quant_merge_prenex.case_0 EoCases.__mk_quant_merge_prenex.case_1
  try unfold Eo.__eo_l_1___mk_quant_merge_prenex
  logos_eq_deep

theorem step_eo__24mk_5fquant_5fmerge_5fprenex_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24mk_5fquant_5fmerge_5fprenex s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__mk_quant_merge_prenex x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __mk_quant_merge_prenex x_a0 x_a1 x_a2 = __mk_quant_merge_prenex y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fquant_5fmerge_5fprenex.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24mk_5fquant_5fmerge_5fprenex
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24mk_5fquant_5fmerge_5fprenex_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24mk_5fquant_5fmerge_5fprenex_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_quant_merge_prenex.case_0 EoCases.__mk_quant_merge_prenex.case_1

theorem body_eo__24mk_5fquant_5fmerge_5fprenex_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fquant_5fmerge_5fprenex s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_quant_merge_prenex x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24mk_5fquant_5fmerge_5fprenex s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_quant_merge_prenex x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24mk_5fquant_5fmerge_5fprenex body_eo__24mk_5fquant_5fmerge_5fprenex_loop
  step with step_eo__24mk_5fquant_5fmerge_5fprenex_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24mk_5fquant_5fmerge_5fprenex at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24mk_5fquant_5fmerge_5fprenex_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fquant_5fmerge_5fprenex.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fquant_5fmerge_5fprenex
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 941#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5fquant_5fmerge_5fprenex s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_quant_merge_prenex x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_941 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_941 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fquant_5fmerge_5fprenex_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fquant_5fminiscope_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fquant_5fminiscope_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_quant_miniscope_and.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_quant_miniscope_and.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fquant_5fminiscope_5fand
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_quant_miniscope_and.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_quant_miniscope_and.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_quant_miniscope_and.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_forall.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24mk_5fquant_5fminiscope_5fand s6 a0 v2 _ _ hinv6 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_mk_rep s7 v11 v12 _ _ hinv7 h64 h_v11 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v13 in EoCases.__mk_quant_miniscope_and.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fquant_5fminiscope_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fquant_5fminiscope_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_quant_miniscope_and.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_quant_miniscope_and.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fquant_5fminiscope_5fand
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_quant_miniscope_and.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__mk_quant_miniscope_and.case_1 using hn_a0 hn_a1

/-- logos's `__mk_quant_miniscope_and` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fquant_5fminiscope_5fand.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_quant_miniscope_and x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_quant_miniscope_and.case_0 x_a0 x_a1, EoCases.__mk_quant_miniscope_and.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_quant_miniscope_and
  unfold EoCases.__mk_quant_miniscope_and.case_0 EoCases.__mk_quant_miniscope_and.case_1
  logos_eq

theorem body_eo__24mk_5fquant_5fminiscope_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fquant_5fminiscope_5fand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_quant_miniscope_and x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fquant_5fminiscope_5fand.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fquant_5fminiscope_5fand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fquant_5fminiscope_5fand_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fquant_5fminiscope_5fand_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_quant_miniscope_and.case_0 EoCases.__mk_quant_miniscope_and.case_1

theorem eo__24mk_5fquant_5fminiscope_5fand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fquant_5fminiscope_5fand.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fquant_5fminiscope_5fand
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 942#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5fquant_5fminiscope_5fand s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_quant_miniscope_and x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_942 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_942 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fquant_5fminiscope_5fand_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fre_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fre_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_re_concat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__mk_re_concat.case_0 x_a0 x_a1 = some (__mk_re_concat y0 y1)
      | core.result.Result.Ok none => EoCases.__mk_re_concat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fre_5fconcat more_0_eo__24mk_5fre_5fconcat
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_re_concat.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_re_concat.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_re_concat.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_re_concat.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_re_concat.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_re_concat.case_0
  pat_unapply h_a1 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__mk_re_concat.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__mk_re_concat.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__mk_re_concat.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v22 (by rw [he_v22]; exact empty_args) hinv4 h64 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s5 v22 v12 _ _ hinv5 h64 h_v22 h_v12 (by ns_tac) (by ns_tac) as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s6 v23 v19 _ _ hinv6 h64 h_v23 h_v19 (by ns_tac) (by ns_tac) as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s7 v21 v24 _ _ hinv7 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s8 e_v26 (by rw [he_v26]; exact empty_args) hinv8 h64 as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s9 v26 v9 _ _ hinv9 h64 h_v26 h_v9 (by ns_tac) (by ns_tac) as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s10 v27 v16 _ _ hinv10 h64 h_v27 h_v16 (by ns_tac) (by ns_tac) as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s11 v25 v28 _ _ hinv11 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s12, hinv12, h_v29⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  case_again hinv12 hG with h_v2 h_v29 in EoCases.__mk_re_concat.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

theorem case_1_eo__24mk_5fre_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fre_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__mk_re_concat.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__mk_re_concat.case_1 x_a0 x_a1 = some (__mk_re_concat y0 y1)
      | core.result.Result.Ok none => EoCases.__mk_re_concat.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fre_5fconcat
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_re_concat.case_1
  pat_unapply h_a1 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__mk_re_concat.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__mk_re_concat.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v5 h_v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__mk_re_concat.case_1
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v6 _ _ hinv3 h64 h_v8 h_v6 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 v3 _ _ hinv4 h64 h_v9 h_v3 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__mk_re_concat.case_1 using hn_a0 hn_a1 hn_v2 hn_v3 hn_v5 hn_v6

/-- logos's `__mk_re_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fre_5fconcat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_re_concat x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_re_concat.case_0 x_a0 x_a1, EoCases.__mk_re_concat.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_re_concat
  unfold EoCases.__mk_re_concat.case_0 EoCases.__mk_re_concat.case_1
  logos_eq

theorem step_eo__24mk_5fre_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24mk_5fre_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__mk_re_concat x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __mk_re_concat x_a0 x_a1 = __mk_re_concat y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fre_5fconcat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24mk_5fre_5fconcat
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24mk_5fre_5fconcat_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24mk_5fre_5fconcat_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_re_concat.case_0 EoCases.__mk_re_concat.case_1

theorem body_eo__24mk_5fre_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fre_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24mk_5fre_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24mk_5fre_5fconcat body_eo__24mk_5fre_5fconcat_loop
  step with step_eo__24mk_5fre_5fconcat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24mk_5fre_5fconcat at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24mk_5fre_5fconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fre_5fconcat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fre_5fconcat
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 944#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24mk_5fre_5fconcat s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_re_concat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_944 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_944 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fre_5fconcat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_re_unfold_neg_concat_fixed.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_re_unfold_neg_concat_fixed.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_neg_concat_fixed.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_neg_concat_fixed.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_re_unfold_neg_concat_fixed.case_0
  have h_ite_v87 := (show if_6_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed s1 a2 a0 v5 a2 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_6_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed more_1_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed more_2_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed more_3_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed more_4_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed more_5_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_a2 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      step as ⟨e_v7, he_v7⟩
      store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo_str_2ein_5fre.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
      store_step with Store.apply_rep s5 v10 a0 _ _ hinv5 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo__2d.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
      step as ⟨e_v13, he_v13⟩
      store_step with CtorSpec.eo_str_2elen.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      store_step with Store.apply_rep s8 v13 a0 _ _ hinv8 h64 h_v13 h_a0 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
      store_step with Store.apply_rep s9 v12 v14 _ _ hinv9 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
      store_step with ih.eo__24str_5ffixed_5flen_5fre s10 v5 _ hinv10 h64 (hG.rem hrem) h_v5 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
      store_step with Store.apply_mk_rep s11 v15 v16 _ _ hinv11 h64 h_v15 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
      store_step with Store.apply_mk_rep s12 v11 v17 _ _ hinv12 h64 h_v11 h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      store_step with ih.eo__24str_5ffixed_5flen_5fre s13 v5 _ hinv13 h64 (hG.rem hrem) h_v5 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      store_step with Store.apply_mk_rep s14 v18 v19 _ _ hinv14 h64 h_v18 h_v19 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      store_step with Store.apply_mk_rep s15 v9 v20 _ _ hinv15 h64 h_v9 h_v20 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      store_step with Store.apply_mk_rep s16 v21 v5 _ _ hinv16 h64 h_v21 h_v5 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      store_step with Store.apply_mk_rep s17 v8 v22 _ _ hinv17 h64 h_v8 h_v22 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      store_step with Store.apply_mk_rep s18 v7 v23 _ _ hinv18 h64 h_v7 h_v23 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
      step as ⟨e_v25, he_v25⟩
      store_step with CtorSpec.eo_or.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo_not.construct s20 e_v26 (by rw [he_v26]; exact empty_args) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo_str_2ein_5fre.construct s21 e_v27 (by rw [he_v27]; exact empty_args) hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s22 e_v28 (by rw [he_v28]; exact empty_args) hinv22 h64 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
      store_step with Store.apply_rep s23 v28 a0 _ _ hinv23 h64 h_v28 h_a0 (by ns_tac) (by ns_tac) as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s24 0#u32 (0) (by scalar_tac) hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
      store_step with Store.apply_rep s25 v29 v30 _ _ hinv25 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
      step as ⟨e_v32, he_v32⟩
      store_step with CtorSpec.eo__2d.construct s26 e_v32 (by rw [he_v32]; exact empty_args) hinv26 h64 as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
      step as ⟨e_v33, he_v33⟩
      store_step with CtorSpec.eo_str_2elen.construct s27 e_v33 (by rw [he_v33]; exact empty_args) hinv27 h64 as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
      store_step with Store.apply_rep s28 v33 a0 _ _ hinv28 h64 h_v33 h_a0 (by ns_tac) (by ns_tac) as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
      store_step with Store.apply_rep s29 v32 v34 _ _ hinv29 h64 h_v32 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
      store_step with ih.eo__24str_5ffixed_5flen_5fre s30 v5 _ hinv30 h64 (hG.rem hrem) h_v5 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
      store_step with Store.apply_mk_rep s31 v35 v36 _ _ hinv31 h64 h_v35 h_v36 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
      store_step with Store.apply_mk_rep s32 v31 v37 _ _ hinv32 h64 h_v31 h_v37 as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
      store_step with Store.apply_mk_rep s33 v27 v38 _ _ hinv33 h64 h_v27 h_v38 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
      step as ⟨e_v40, he_v40⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s34 e_v40 (by rw [he_v40]; exact empty_args) hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
      have h_ite_v43 := (show if_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed s35 a2 v2 ⦃ r s' => s'.Inv ∧ s35.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s35
        rcases Store.boolean_value_term h_a2 with ⟨hx_41, hbv_41⟩ | ⟨hx_41, hbv_41⟩ | ⟨hx_41, hbv_41⟩
        · ite_branch hbv_41
          step as ⟨e_v41, he_v41⟩
          store_step with CtorSpec.eo_re_2e_2b_2b.construct s35 e_v41 (by rw [he_v41]; exact empty_args) hinv35 h64 as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
          step as ⟨e_v42, he_v42⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s36 e_v42 (by rw [he_v42]; rfl) h_v41 h_v2 hinv36 h64 (hG.rem hrem) (by not_left_tac) as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
          ite_done hinv37 hG with (eo_ite_true_rep _ hx_41 h_v42)
        · ite_branch hbv_41
          ite_done hinv35 hG with (eo_ite_false_rep _ hx_41 h_v2)
        · ite_branch hbv_41
          ite_stuck hinv35 hG with hx_41)
      store_step with h_ite_v43 as ⟨v43, s36, hinv36, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
      step as ⟨e_v44, he_v44⟩
      store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s36 e_v44 (by rw [he_v44]; rfl) h_v40 h_v43 hinv36 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v44, s37, hinv37, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43
      store_step with Store.apply_mk_rep s37 v39 v44 _ _ hinv37 h64 h_v39 h_v44 as ⟨v45, s38, hinv38, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43 h_v44
      store_step with Store.apply_mk_rep s38 v26 v45 _ _ hinv38 h64 h_v26 h_v45 as ⟨v46, s39, hinv39, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43 h_v44 h_v45
      store_step with Store.apply_mk_rep s39 v25 v46 _ _ hinv39 h64 h_v25 h_v46 as ⟨v47, s40, hinv40, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43 h_v44 h_v45 h_v46
      store_step with Store.literal_boolean_spec s40 false hinv40 h64 as ⟨v48, s41, hinv41, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43 h_v44 h_v45 h_v46 h_v47
      store_step with Store.apply_mk_rep s41 v47 v48 _ _ hinv41 h64 h_v47 h_v48 as ⟨v49, s42, hinv42, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
      store_step with Store.apply_mk_rep s42 v24 v49 _ _ hinv42 h64 h_v24 h_v49 as ⟨v50, s43, hinv43, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
      ite_done hinv43 hG with (eo_ite_true_rep _ hx_7 h_v50)
    · ite_branch hbv_7
      step as ⟨e_v51, he_v51⟩
      store_step with CtorSpec.eo_or.construct s1 e_v51 (by rw [he_v51]; exact empty_args) hinv1 h64 as ⟨v51, s2, hinv2, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
      step as ⟨e_v52, he_v52⟩
      store_step with CtorSpec.eo_not.construct s2 e_v52 (by rw [he_v52]; exact empty_args) hinv2 h64 as ⟨v52, s3, hinv3, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51
      step as ⟨e_v53, he_v53⟩
      store_step with CtorSpec.eo_str_2ein_5fre.construct s3 e_v53 (by rw [he_v53]; exact empty_args) hinv3 h64 as ⟨v53, s4, hinv4, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52
      step as ⟨e_v54, he_v54⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s4 e_v54 (by rw [he_v54]; exact empty_args) hinv4 h64 as ⟨v54, s5, hinv5, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53
      store_step with Store.apply_rep s5 v54 a0 _ _ hinv5 h64 h_v54 h_a0 (by ns_tac) (by ns_tac) as ⟨v55, s6, hinv6, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v56, s7, hinv7, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55
      store_step with Store.apply_rep s7 v55 v56 _ _ hinv7 h64 h_v55 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s8, hinv8, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
      store_step with ih.eo__24str_5ffixed_5flen_5fre s8 v5 _ hinv8 h64 (hG.rem hrem) h_v5 as ⟨v58, s9, hinv9, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
      store_step with Store.apply_mk_rep s9 v57 v58 _ _ hinv9 h64 h_v57 h_v58 as ⟨v59, s10, hinv10, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
      store_step with Store.apply_mk_rep s10 v53 v59 _ _ hinv10 h64 h_v53 h_v59 as ⟨v60, s11, hinv11, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
      store_step with Store.apply_mk_rep s11 v60 v5 _ _ hinv11 h64 h_v60 h_v5 as ⟨v61, s12, hinv12, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
      store_step with Store.apply_mk_rep s12 v52 v61 _ _ hinv12 h64 h_v52 h_v61 as ⟨v62, s13, hinv13, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
      store_step with Store.apply_mk_rep s13 v51 v62 _ _ hinv13 h64 h_v51 h_v62 as ⟨v63, s14, hinv14, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
      step as ⟨e_v64, he_v64⟩
      store_step with CtorSpec.eo_or.construct s14 e_v64 (by rw [he_v64]; exact empty_args) hinv14 h64 as ⟨v64, s15, hinv15, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
      step as ⟨e_v65, he_v65⟩
      store_step with CtorSpec.eo_not.construct s15 e_v65 (by rw [he_v65]; exact empty_args) hinv15 h64 as ⟨v65, s16, hinv16, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
      step as ⟨e_v66, he_v66⟩
      store_step with CtorSpec.eo_str_2ein_5fre.construct s16 e_v66 (by rw [he_v66]; exact empty_args) hinv16 h64 as ⟨v66, s17, hinv17, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
      step as ⟨e_v67, he_v67⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s17 e_v67 (by rw [he_v67]; exact empty_args) hinv17 h64 as ⟨v67, s18, hinv18, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
      store_step with Store.apply_rep s18 v67 a0 _ _ hinv18 h64 h_v67 h_a0 (by ns_tac) (by ns_tac) as ⟨v68, s19, hinv19, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
      store_step with ih.eo__24str_5ffixed_5flen_5fre s19 v5 _ hinv19 h64 (hG.rem hrem) h_v5 as ⟨v69, s20, hinv20, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
      store_step with Store.apply_mk_rep s20 v68 v69 _ _ hinv20 h64 h_v68 h_v69 as ⟨v70, s21, hinv21, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
      step as ⟨e_v71, he_v71⟩
      store_step with CtorSpec.eo__2d.construct s21 e_v71 (by rw [he_v71]; exact empty_args) hinv21 h64 as ⟨v71, s22, hinv22, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
      step as ⟨e_v72, he_v72⟩
      store_step with CtorSpec.eo_str_2elen.construct s22 e_v72 (by rw [he_v72]; exact empty_args) hinv22 h64 as ⟨v72, s23, hinv23, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71
      store_step with Store.apply_rep s23 v72 a0 _ _ hinv23 h64 h_v72 h_a0 (by ns_tac) (by ns_tac) as ⟨v73, s24, hinv24, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72
      store_step with Store.apply_rep s24 v71 v73 _ _ hinv24 h64 h_v71 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s25, hinv25, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73
      store_step with ih.eo__24str_5ffixed_5flen_5fre s25 v5 _ hinv25 h64 (hG.rem hrem) h_v5 as ⟨v75, s26, hinv26, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74
      store_step with Store.apply_mk_rep s26 v74 v75 _ _ hinv26 h64 h_v74 h_v75 as ⟨v76, s27, hinv27, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75
      store_step with Store.apply_mk_rep s27 v70 v76 _ _ hinv27 h64 h_v70 h_v76 as ⟨v77, s28, hinv28, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76
      store_step with Store.apply_mk_rep s28 v66 v77 _ _ hinv28 h64 h_v66 h_v77 as ⟨v78, s29, hinv29, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77
      step as ⟨e_v79, he_v79⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s29 e_v79 (by rw [he_v79]; exact empty_args) hinv29 h64 as ⟨v79, s30, hinv30, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78
      step as ⟨e_v80, he_v80⟩
      store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s30 e_v80 (by rw [he_v80]; rfl) h_v79 h_v2 hinv30 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v80, s31, hinv31, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79
      store_step with Store.apply_mk_rep s31 v78 v80 _ _ hinv31 h64 h_v78 h_v80 as ⟨v81, s32, hinv32, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80
      store_step with Store.apply_mk_rep s32 v65 v81 _ _ hinv32 h64 h_v65 h_v81 as ⟨v82, s33, hinv33, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81
      store_step with Store.apply_mk_rep s33 v64 v82 _ _ hinv33 h64 h_v64 h_v82 as ⟨v83, s34, hinv34, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82
      store_step with Store.literal_boolean_spec s34 false hinv34 h64 as ⟨v84, s35, hinv35, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83
      store_step with Store.apply_mk_rep s35 v83 v84 _ _ hinv35 h64 h_v83 h_v84 as ⟨v85, s36, hinv36, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84
      store_step with Store.apply_mk_rep s36 v63 v85 _ _ hinv36 h64 h_v63 h_v85 as ⟨v86, s37, hinv37, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85
      ite_done hinv37 hG with (eo_ite_false_rep _ hx_7 h_v86)
    · ite_branch hbv_7
      ite_stuck hinv1 hG with hx_7)
  store_step with h_ite_v87 as ⟨v87, s2, hinv2, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv2 hG with h_v87 in EoCases.__mk_re_unfold_neg_concat_fixed.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__mk_re_unfold_neg_concat_fixed` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_re_unfold_neg_concat_fixed x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_re_unfold_neg_concat_fixed.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_re_unfold_neg_concat_fixed
  unfold EoCases.__mk_re_unfold_neg_concat_fixed.case_0
  logos_eq

theorem body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_unfold_neg_concat_fixed x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__mk_re_unfold_neg_concat_fixed.case_0

theorem eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_re_unfold_neg_concat_fixed x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fre_5funfold_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fre_5funfold_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_re_unfold_pos.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_re_unfold_pos.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fre_5funfold_5fpos more_0_eo__24mk_5fre_5funfold_5fpos more_1_eo__24mk_5fre_5funfold_5fpos more_2_eo__24mk_5fre_5funfold_5fpos more_3_eo__24mk_5fre_5funfold_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_pos.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_re_unfold_pos.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_re_2ediff.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s5 _ _ rfl hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s6 v7 v8 _ _ hinv6 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s7 v6 v9 _ _ hinv7 h64 h_v6 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s8 v4 v10 _ _ hinv8 h64 h_v4 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s10 e_v13 (by rw [he_v13]; exact empty_args) hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s11 v13 v2 _ _ hinv11 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s12 v12 v14 _ _ hinv12 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s13 e_v16 (by rw [he_v16]; exact empty_args) hinv13 h64 as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_re_2ediff.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s15 v17 v2 _ _ hinv15 h64 h_v17 h_v2 (by ns_tac) (by ns_tac) as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s16 e_v19 (by rw [he_v19]; exact empty_args) hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s17 _ _ rfl hinv17 h64 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s18 v19 v20 _ _ hinv18 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s19 v18 v21 _ _ hinv19 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s20 v16 v22 _ _ hinv20 h64 h_v16 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s21 e_v24 (by rw [he_v24]; exact empty_args) hinv21 h64 as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s22 _ _ rfl hinv22 h64 as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s23 v24 v25 _ _ hinv23 h64 h_v24 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s24 v23 v26 _ _ hinv24 h64 h_v23 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s25 v15 v27 _ _ hinv25 h64 h_v15 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s26 v11 v28 _ _ hinv26 h64 h_v11 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s27 e_v30 (by rw [he_v30]; exact empty_args) hinv27 h64 as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_re_2ediff.construct s28 e_v31 (by rw [he_v31]; exact empty_args) hinv28 h64 as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s29 v31 v2 _ _ hinv29 h64 h_v31 h_v2 (by ns_tac) (by ns_tac) as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s30 e_v33 (by rw [he_v33]; exact empty_args) hinv30 h64 as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s31 _ _ rfl hinv31 h64 as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s32 v33 v34 _ _ hinv32 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s33 v32 v35 _ _ hinv33 h64 h_v32 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s34 v30 v36 _ _ hinv34 h64 h_v30 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s35 e_v38 (by rw [he_v38]; exact empty_args) hinv35 h64 as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s36 e_v39 (by rw [he_v39]; exact empty_args) hinv36 h64 as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s37 v39 v2 _ _ hinv37 h64 h_v39 h_v2 (by ns_tac) (by ns_tac) as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s38 v38 v40 _ _ hinv38 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s39 e_v42 (by rw [he_v42]; exact empty_args) hinv39 h64 as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_re_2ediff.construct s40 e_v43 (by rw [he_v43]; exact empty_args) hinv40 h64 as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s41 v43 v2 _ _ hinv41 h64 h_v43 h_v2 (by ns_tac) (by ns_tac) as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s42 e_v45 (by rw [he_v45]; exact empty_args) hinv42 h64 as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s43 _ _ rfl hinv43 h64 as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s44 v45 v46 _ _ hinv44 h64 h_v45 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s45 v44 v47 _ _ hinv45 h64 h_v44 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s46 v42 v48 _ _ hinv46 h64 h_v42 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s47 e_v50 (by rw [he_v50]; exact empty_args) hinv47 h64 as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s48 _ _ rfl hinv48 h64 as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s49 v50 v51 _ _ hinv49 h64 h_v50 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s50 v49 v52 _ _ hinv50 h64 h_v49 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s51 v41 v53 _ _ hinv51 h64 h_v41 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s52 v37 v54 _ _ hinv52 h64 h_v37 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s53 0#u32 (0) (by scalar_tac) hinv53 h64 as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with ih.eo__24re_5funfold_5fpos_5fconcat_5frec s54 a0 v29 v55 v56 _ _ _ _ hinv54 h64 (hG.rem hrem) h_a0 h_v29 h_v55 h_v56 as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with ih.eo__24mk_5fre_5funfold_5fpos_5fstar s55 a0 v2 v57 _ _ _ hinv55 h64 (hG.rem hrem) h_a0 h_v2 h_v57 as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  case_done hinv56 hG with h_v58 in EoCases.__mk_re_unfold_pos.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24mk_5fre_5funfold_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fre_5funfold_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_re_unfold_pos.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_re_unfold_pos.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fre_5funfold_5fpos more_6_eo__24mk_5fre_5funfold_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_pos.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_pos.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_re_unfold_pos.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v10 v5 _ _ hinv5 h64 h_v10 h_v5 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s6 v11 v2 _ _ hinv6 h64 h_v11 h_v2 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with ih.eo__24re_5funfold_5fpos_5fconcat_5frec s8 a0 v9 v12 v13 _ _ _ _ hinv8 h64 (hG.rem hrem) h_a0 h_v9 h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with ih.eo__24pair_5fsecond s9 v14 _ hinv9 h64 (hG.rem hrem) h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_eq s11 e_v17 (by rw [he_v17]; rfl) h_v15 h_v16 hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  have h_ite_v54 := (show if_5_eo__24mk_5fre_5funfold_5fpos s12 v17 a0 v5 v2 ⦃ r s' => s'.Inv ∧ s12.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_5_eo__24mk_5fre_5funfold_5fpos more_4_eo__24mk_5fre_5funfold_5fpos
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s12
    rcases Store.boolean_value_term h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
    · ite_branch hbv_18
      step as ⟨e_v18, he_v18⟩
      store_step with CtorSpec.eo__3d.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      store_step with Store.apply_rep s13 v18 a0 _ _ hinv13 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      step as ⟨e_v20, he_v20⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      store_step with Store.apply_rep s15 v20 v5 _ _ hinv15 h64 h_v20 h_v5 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      store_step with Store.apply_rep s16 v21 v2 _ _ hinv16 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s17 e_v23 (by rw [he_v23]; exact empty_args) hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      store_step with Store.apply_rep s18 v23 v5 _ _ hinv18 h64 h_v23 h_v5 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
      store_step with Store.apply_rep s19 v24 v2 _ _ hinv19 h64 h_v24 h_v2 (by ns_tac) (by ns_tac) as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s20 0#u32 (0) (by scalar_tac) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
      store_step with ih.eo__24re_5funfold_5fpos_5fconcat_5frec s21 a0 v22 v25 v26 _ _ _ _ hinv21 h64 (hG.rem hrem) h_a0 h_v22 h_v25 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
      store_step with ih.eo__24pair_5ffirst s22 v27 _ hinv22 h64 (hG.rem hrem) h_v27 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
      store_step with Store.apply_mk_rep s23 v19 v28 _ _ hinv23 h64 h_v19 h_v28 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
      ite_done hinv24 hG with (eo_ite_true_rep _ hx_18 h_v29)
    · ite_branch hbv_18
      step as ⟨e_v30, he_v30⟩
      store_step with CtorSpec.eo_and.construct s12 e_v30 (by rw [he_v30]; exact empty_args) hinv12 h64 as ⟨v30, s13, hinv13, h_v30⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      step as ⟨e_v31, he_v31⟩
      store_step with CtorSpec.eo__3d.construct s13 e_v31 (by rw [he_v31]; exact empty_args) hinv13 h64 as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30
      store_step with Store.apply_rep s14 v31 a0 _ _ hinv14 h64 h_v31 h_a0 (by ns_tac) (by ns_tac) as ⟨v32, s15, hinv15, h_v32⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31
      step as ⟨e_v33, he_v33⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s15 e_v33 (by rw [he_v33]; exact empty_args) hinv15 h64 as ⟨v33, s16, hinv16, h_v33⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32
      store_step with Store.apply_rep s16 v33 v5 _ _ hinv16 h64 h_v33 h_v5 (by ns_tac) (by ns_tac) as ⟨v34, s17, hinv17, h_v34⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33
      store_step with Store.apply_rep s17 v34 v2 _ _ hinv17 h64 h_v34 h_v2 (by ns_tac) (by ns_tac) as ⟨v35, s18, hinv18, h_v35⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34
      step as ⟨e_v36, he_v36⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s18 e_v36 (by rw [he_v36]; exact empty_args) hinv18 h64 as ⟨v36, s19, hinv19, h_v36⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
      store_step with Store.apply_rep s19 v36 v5 _ _ hinv19 h64 h_v36 h_v5 (by ns_tac) (by ns_tac) as ⟨v37, s20, hinv20, h_v37⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
      store_step with Store.apply_rep s20 v37 v2 _ _ hinv20 h64 h_v37 h_v2 (by ns_tac) (by ns_tac) as ⟨v38, s21, hinv21, h_v38⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s21 0#u32 (0) (by scalar_tac) hinv21 h64 as ⟨v39, s22, hinv22, h_v39⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
      store_step with ih.eo__24re_5funfold_5fpos_5fconcat_5frec s22 a0 v35 v38 v39 _ _ _ _ hinv22 h64 (hG.rem hrem) h_a0 h_v35 h_v38 h_v39 as ⟨v40, s23, hinv23, h_v40⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
      store_step with ih.eo__24pair_5ffirst s23 v40 _ hinv23 h64 (hG.rem hrem) h_v40 as ⟨v41, s24, hinv24, h_v41⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
      store_step with Store.apply_mk_rep s24 v32 v41 _ _ hinv24 h64 h_v32 h_v41 as ⟨v42, s25, hinv25, h_v42⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
      store_step with Store.apply_mk_rep s25 v30 v42 _ _ hinv25 h64 h_v30 h_v42 as ⟨v43, s26, hinv26, h_v43⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
      step as ⟨e_v44, he_v44⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s26 e_v44 (by rw [he_v44]; exact empty_args) hinv26 h64 as ⟨v44, s27, hinv27, h_v44⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
      store_step with Store.apply_rep s27 v44 v5 _ _ hinv27 h64 h_v44 h_v5 (by ns_tac) (by ns_tac) as ⟨v45, s28, hinv28, h_v45⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
      store_step with Store.apply_rep s28 v45 v2 _ _ hinv28 h64 h_v45 h_v2 (by ns_tac) (by ns_tac) as ⟨v46, s29, hinv29, h_v46⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
      step as ⟨e_v47, he_v47⟩
      store_step with CtorSpec.eo_re_2e_2b_2b.construct s29 e_v47 (by rw [he_v47]; exact empty_args) hinv29 h64 as ⟨v47, s30, hinv30, h_v47⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
      store_step with Store.apply_rep s30 v47 v5 _ _ hinv30 h64 h_v47 h_v5 (by ns_tac) (by ns_tac) as ⟨v48, s31, hinv31, h_v48⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
      store_step with Store.apply_rep s31 v48 v2 _ _ hinv31 h64 h_v48 h_v2 (by ns_tac) (by ns_tac) as ⟨v49, s32, hinv32, h_v49⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v50, s33, hinv33, h_v50⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
      store_step with ih.eo__24re_5funfold_5fpos_5fconcat_5frec s33 a0 v46 v49 v50 _ _ _ _ hinv33 h64 (hG.rem hrem) h_a0 h_v46 h_v49 h_v50 as ⟨v51, s34, hinv34, h_v51⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
      store_step with ih.eo__24pair_5fsecond s34 v51 _ hinv34 h64 (hG.rem hrem) h_v51 as ⟨v52, s35, hinv35, h_v52⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
      store_step with Store.apply_mk_rep s35 v43 v52 _ _ hinv35 h64 h_v43 h_v52 as ⟨v53, s36, hinv36, h_v53⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
      ite_done hinv36 hG with (eo_ite_false_rep _ hx_18 h_v53)
    · ite_branch hbv_18
      ite_stuck hinv12 hG with hx_18)
  store_step with h_ite_v54 as ⟨v54, s13, hinv13, h_v54⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv13 hG with h_v54 in EoCases.__mk_re_unfold_pos.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__mk_re_unfold_pos` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fre_5funfold_5fpos.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __mk_re_unfold_pos x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_re_unfold_pos.case_0 x_a0 x_a1, EoCases.__mk_re_unfold_pos.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __mk_re_unfold_pos
  unfold EoCases.__mk_re_unfold_pos.case_0 EoCases.__mk_re_unfold_pos.case_1
  logos_eq

theorem body_eo__24mk_5fre_5funfold_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24mk_5fre_5funfold_5fpos s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_unfold_pos x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fre_5funfold_5fpos.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24mk_5fre_5funfold_5fpos
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24mk_5fre_5funfold_5fpos_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24mk_5fre_5funfold_5fpos_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__mk_re_unfold_pos.case_0 EoCases.__mk_re_unfold_pos.case_1

theorem eo__24mk_5fre_5funfold_5fpos_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fre_5funfold_5fpos.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24mk_5fre_5funfold_5fpos
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fre_5funfold_5fpos s1 a0 a1) (fun s' t => Represents.rep s' t (__mk_re_unfold_pos x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fre_5funfold_5fpos_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fre_5funfold_5fpos_5fstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fre_5funfold_5fpos_5fstar s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_re_unfold_pos_star.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_re_unfold_pos_star.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fre_5funfold_5fpos_5fstar more_0_eo__24mk_5fre_5funfold_5fpos_5fstar more_1_eo__24mk_5fre_5funfold_5fpos_5fstar more_2_eo__24mk_5fre_5funfold_5fpos_5fstar more_3_eo__24mk_5fre_5funfold_5fpos_5fstar
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_re_unfold_pos_star.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_re_unfold_pos_star.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v9 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__mk_re_unfold_pos_star.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v16 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__mk_re_unfold_pos_star.case_0
  pat_unapply h_v22 as ⟨v25, v26, x_v25, x_v26, h_v25, h_v26, hn_v25, hn_v26⟩ using hinv3 else hinv3 hG in EoCases.__mk_re_unfold_pos_star.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v27 (by rw [he_v27]; exact empty_args) hinv3 h64 as ⟨v27, s4, hinv4, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26
  pat_same v25 v27 with h_v25 h_v27 using hinv4 else hinv4 hG in EoCases.__mk_re_unfold_pos_star.case_0
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s4 _ _ rfl hinv4 h64 as ⟨v28, s5, hinv5, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27
  pat_same v23 v28 with h_v23 h_v28 using hinv5 else hinv5 hG in EoCases.__mk_re_unfold_pos_star.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_or.construct s5 e_v29 (by rw [he_v29]; exact empty_args) hinv5 h64 as ⟨v29, s6, hinv6, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v30 (by rw [he_v30]; exact empty_args) hinv6 h64 as ⟨v30, s7, hinv7, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s7 v30 a0 _ _ hinv7 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s8, hinv8, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s8 _ _ rfl hinv8 h64 as ⟨v32, s9, hinv9, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s9 v31 v32 _ _ hinv9 h64 h_v31 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s10, hinv10, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s10 v29 v33 _ _ hinv10 h64 h_v29 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s11, hinv11, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_or.construct s11 e_v35 (by rw [he_v35]; exact empty_args) hinv11 h64 as ⟨v35, s12, hinv12, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s12 e_v36 (by rw [he_v36]; exact empty_args) hinv12 h64 as ⟨v36, s13, hinv13, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s13 v36 a0 _ _ hinv13 h64 h_v36 h_a0 (by ns_tac) (by ns_tac) as ⟨v37, s14, hinv14, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s14 v37 a1 _ _ hinv14 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s15, hinv15, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s15 v35 v38 _ _ hinv15 h64 h_v35 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s16, hinv16, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_or.construct s16 e_v40 (by rw [he_v40]; exact empty_args) hinv16 h64 as ⟨v40, s17, hinv17, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_and.construct s17 e_v41 (by rw [he_v41]; exact empty_args) hinv17 h64 as ⟨v41, s18, hinv18, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s18 e_v42 (by rw [he_v42]; exact empty_args) hinv18 h64 as ⟨v42, s19, hinv19, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s19 v42 a0 _ _ hinv19 h64 h_v42 h_a0 (by ns_tac) (by ns_tac) as ⟨v43, s20, hinv20, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s20 e_v44 (by rw [he_v44]; exact empty_args) hinv20 h64 as ⟨v44, s21, hinv21, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s21 v44 v12 _ _ hinv21 h64 h_v44 h_v12 (by ns_tac) (by ns_tac) as ⟨v45, s22, hinv22, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v46 (by rw [he_v46]; exact empty_args) hinv22 h64 as ⟨v46, s23, hinv23, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s23 v46 v19 _ _ hinv23 h64 h_v46 h_v19 (by ns_tac) (by ns_tac) as ⟨v47, s24, hinv24, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s24 e_v48 (by rw [he_v48]; exact empty_args) hinv24 h64 as ⟨v48, s25, hinv25, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s25 v48 v26 _ _ hinv25 h64 h_v48 h_v26 (by ns_tac) (by ns_tac) as ⟨v49, s26, hinv26, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s26 _ _ rfl hinv26 h64 as ⟨v50, s27, hinv27, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s27 v49 v50 _ _ hinv27 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s28, hinv28, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s28 v47 v51 _ _ hinv28 h64 h_v47 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s29, hinv29, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s29 v45 v52 _ _ hinv29 h64 h_v45 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s30, hinv30, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s30 v43 v53 _ _ hinv30 h64 h_v43 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s31, hinv31, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s31 v41 v54 _ _ hinv31 h64 h_v41 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s32, hinv32, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s32 v55 v2 _ _ hinv32 h64 h_v55 h_v2 (by ns_tac) (by ns_tac) as ⟨v56, s33, hinv33, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s33 v40 v56 _ _ hinv33 h64 h_v40 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s34, hinv34, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.literal_boolean_spec s34 false hinv34 h64 as ⟨v58, s35, hinv35, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s35 v57 v58 _ _ hinv35 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s36, hinv36, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  store_step with Store.apply_rep s36 v39 v59 _ _ hinv36 h64 h_v39 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s37, hinv37, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s37 v34 v60 _ _ hinv37 h64 h_v34 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s38, hinv38, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v15 h_v16 h_v18 h_v19 h_v20 h_v22 h_v23 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  case_done hinv38 hG with h_v61 in EoCases.__mk_re_unfold_pos_star.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19 hn_v22 hn_v23 hn_v25 hn_v26

/-- logos's `__mk_re_unfold_pos_star` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fre_5funfold_5fpos_5fstar.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_re_unfold_pos_star x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_re_unfold_pos_star.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_re_unfold_pos_star
  unfold EoCases.__mk_re_unfold_pos_star.case_0
  logos_eq

theorem body_eo__24mk_5fre_5funfold_5fpos_5fstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fre_5funfold_5fpos_5fstar s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_re_unfold_pos_star x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fre_5funfold_5fpos_5fstar.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5fre_5funfold_5fpos_5fstar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5fre_5funfold_5fpos_5fstar_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__mk_re_unfold_pos_star.case_0

theorem eo__24mk_5fre_5funfold_5fpos_5fstar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fre_5funfold_5fpos_5fstar.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fre_5funfold_5fpos_5fstar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fre_5funfold_5fpos_5fstar s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_re_unfold_pos_star x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fre_5funfold_5fpos_5fstar_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fskolems_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fskolems s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_skolems.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_skolems.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fskolems
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_skolems.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_skolems.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_skolems.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__40quantifiers_5fskolemize.construct s2 e_v8 (by rw [he_v8]; rfl) h_a1 h_a2 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_add s5 e_v11 (by rw [he_v11]; rfl) h_a2 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24mk_5fskolems s6 v2 a1 v11 _ _ _ hinv6 h64 (hG.rem hrem) h_v2 h_a1 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_mk_rep s7 v9 v12 _ _ hinv7 h64 h_v9 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v13 in EoCases.__mk_skolems.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fskolems_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fskolems s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_skolems.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_skolems.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fskolems
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_skolems.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__mk_skolems.case_1 using hn_a0 hn_a1 hn_a2

/-- logos's `__mk_skolems` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fskolems.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_skolems x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_skolems.case_0 x_a0 x_a1 x_a2, EoCases.__mk_skolems.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_skolems
  unfold EoCases.__mk_skolems.case_0 EoCases.__mk_skolems.case_1
  logos_eq

theorem body_eo__24mk_5fskolems_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5fskolems s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_skolems x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fskolems.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5fskolems
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5fskolems_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5fskolems_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_skolems.case_0 EoCases.__mk_skolems.case_1

theorem eo__24mk_5fskolems_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fskolems.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5fskolems
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 949#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5fskolems s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_skolems x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_949 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_949 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fskolems_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_symm.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_symm.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_symm.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_symm.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_symm.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v2 _ _ hinv2 h64 h_v7 h_v2 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__mk_symm.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24mk_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_symm.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_symm.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_symm.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__mk_symm.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__mk_symm.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_symm.case_1
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__mk_symm.case_1
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_not.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s4 v12 v6 _ _ hinv4 h64 h_v12 h_v6 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s5 v13 v9 _ _ hinv5 h64 h_v13 h_v9 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s6 v11 v14 _ _ hinv6 h64 h_v11 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv7 hG with h_v15 in EoCases.__mk_symm.case_1 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v8 hn_v9

/-- logos's `__mk_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5fsymm.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __mk_symm x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_symm.case_0 x_a0, EoCases.__mk_symm.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __mk_symm
  unfold EoCases.__mk_symm.case_0 EoCases.__mk_symm.case_1
  logos_eq

theorem body_eo__24mk_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24mk_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_symm x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5fsymm.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24mk_5fsymm_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24mk_5fsymm_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__mk_symm.case_0 EoCases.__mk_symm.case_1

theorem eo__24mk_5fsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5fsymm.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24mk_5fsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24mk_5fsymm s1 a0) (fun s' t => Represents.rep s' t (__mk_symm x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5fsymm_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24mk_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_trans.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_trans.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24mk_5ftrans
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__mk_trans.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__mk_trans.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__mk_trans.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__mk_trans.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__mk_trans.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__mk_trans.case_0
  have h_req_v15 := (show requires_0_eo__24mk_5ftrans s2 a1 v12 a0 v9 v2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24mk_5ftrans
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same a1 v12 with h_a1 h_v12 using hinv2 hG
    req_stuck h_a1 as hq_a1 using hinv2 hG
    store_step with ih.eo__24mk_5ftrans s2 a0 v9 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v9 h_v2 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
    req_done hinv3 hG with h_v14 using hq_a1)
  store_step with h_req_v15 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  case_done hinv4 hG with h_v15 in EoCases.__mk_trans.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24mk_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_trans.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_trans.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24mk_5ftrans
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__mk_trans.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__mk_trans.case_1 using hn_a0 hn_a1 hn_a2

/-- logos's `__mk_trans` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24mk_5ftrans.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __mk_trans x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__mk_trans.case_0 x_a0 x_a1 x_a2, EoCases.__mk_trans.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __mk_trans
  unfold EoCases.__mk_trans.case_0 EoCases.__mk_trans.case_1
  logos_eq

theorem body_eo__24mk_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__mk_trans x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24mk_5ftrans.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24mk_5ftrans
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24mk_5ftrans_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24mk_5ftrans_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__mk_trans.case_0 EoCases.__mk_trans.case_1

theorem eo__24mk_5ftrans_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24mk_5ftrans.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24mk_5ftrans
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 952#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24mk_5ftrans s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__mk_trans x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_952 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_952 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24mk_5ftrans_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24pair_5ffirst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24pair_5ffirst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__pair_first.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__pair_first.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24pair_5ffirst
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__pair_first.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__pair_first.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__pair_first.case_0
  case_done hinv1 hG with h_v5 in EoCases.__pair_first.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__pair_first` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24pair_5ffirst.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __pair_first x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__pair_first.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __pair_first
  unfold EoCases.__pair_first.case_0
  logos_eq

theorem body_eo__24pair_5ffirst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24pair_5ffirst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__pair_first x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24pair_5ffirst.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24pair_5ffirst
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24pair_5ffirst_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__pair_first.case_0

theorem eo__24pair_5ffirst_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24pair_5ffirst.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24pair_5ffirst
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24pair_5ffirst s1 a0) (fun s' t => Represents.rep s' t (__pair_first x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24pair_5ffirst_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24pair_5fsecond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24pair_5fsecond s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__pair_second.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__pair_second.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24pair_5fsecond
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__pair_second.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__pair_second.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__pair_second.case_0
  case_done hinv1 hG with h_v2 in EoCases.__pair_second.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__pair_second` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24pair_5fsecond.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __pair_second x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__pair_second.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __pair_second
  unfold EoCases.__pair_second.case_0
  logos_eq

theorem body_eo__24pair_5fsecond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24pair_5fsecond s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__pair_second x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24pair_5fsecond.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24pair_5fsecond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24pair_5fsecond_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__pair_second.case_0

theorem eo__24pair_5fsecond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24pair_5fsecond.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24pair_5fsecond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24pair_5fsecond s1 a0) (fun s' t => Represents.rep s' t (__pair_second x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24pair_5fsecond_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24poly_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24poly_5fneg s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__poly_neg.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__poly_neg.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24poly_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40poly_2ezero.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__poly_neg.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40poly_2ezero.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__poly_neg.case_0 using hn_a0

theorem case_1_eo__24poly_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24poly_5fneg s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__poly_neg.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__poly_neg.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24poly_5fneg more_0_eo__24poly_5fneg
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__poly_neg.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__poly_neg.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40poly.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__poly_neg.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__poly_neg.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__poly_neg.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40_40mon.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__poly_neg.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40_40poly.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__40_40mon.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s4 v15 v12 _ _ hinv4 h64 h_v15 h_v12 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_neg s5 e_v17 (by rw [he_v17]; rfl) h_v9 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_mk_rep s6 v16 v17 _ _ hinv6 h64 h_v16 h_v17 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_mk_rep s7 v14 v18 _ _ hinv7 h64 h_v14 h_v18 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with ih.eo__24poly_5fneg s8 v2 _ hinv8 h64 (hG.rem hrem) h_v2 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s9 v19 v20 _ _ hinv9 h64 h_v19 h_v20 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv10 hG with h_v21 in EoCases.__poly_neg.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__poly_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24poly_5fneg.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __poly_neg x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__poly_neg.case_0 x_a0, EoCases.__poly_neg.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __poly_neg
  unfold EoCases.__poly_neg.case_0 EoCases.__poly_neg.case_1
  logos_eq

theorem body_eo__24poly_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24poly_5fneg s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__poly_neg x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24poly_5fneg.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24poly_5fneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24poly_5fneg_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24poly_5fneg_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__poly_neg.case_0 EoCases.__poly_neg.case_1

theorem eo__24poly_5fneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24poly_5fneg.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24poly_5fneg
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 961#u32 _ [a0] rfl
    (fun s1 => body_eo__24poly_5fneg s1 a0) (fun s' t => Represents.rep s' t (__poly_neg x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_961 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_961 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24poly_5fneg_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_concat_merge.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24re_5fconcat_5fmerge more_0_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_concat_merge.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_concat_merge.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__re_concat_merge.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s4 v15 v5 _ _ hinv4 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s5 v16 v2 _ _ hinv5 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s6 e_v18 (by rw [he_v18]; exact empty_args) hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s7 v18 v12 _ _ hinv7 h64 h_v18 h_v12 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s8 v19 v9 _ _ hinv8 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s9 e_v21 (by rw [he_v21]; rfl) h_v14 h_v17 h_v20 hinv9 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv10 hG with h_v21 in EoCases.__re_concat_merge.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

theorem case_1_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_concat_merge.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2enone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__re_concat_merge.case_1 using hn_a0 hn_a1

theorem case_2_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_concat_merge.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_concat_merge.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_concat_merge.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 a0 _ _ hinv2 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__re_concat_merge.case_2 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_3_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_3_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_concat_merge.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_concat_merge.case_3
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_3
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s1 _ _ rfl hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__re_concat_merge.case_3
  case_done hinv2 hG with h_a1 in EoCases.__re_concat_merge.case_3 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_4_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_4_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_concat_merge.case_4 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_concat_merge.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_concat_merge.case_4
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s1 _ _ rfl hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__re_concat_merge.case_4
  case_done hinv2 hG with h_a0 in EoCases.__re_concat_merge.case_4 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_5_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_5_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_concat_merge.case_5 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_5 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s5 _ _ rfl hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__re_concat_merge.case_5 using hn_a0 hn_a1

theorem cases_0_0_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_0 x_a0 x_a1 = none ∧ EoCases.__re_concat_merge.case_1 x_a0 x_a1 = none ∧ EoCases.__re_concat_merge.case_2 x_a0 x_a1 = none ∧ EoCases.__re_concat_merge.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24re_5fconcat_5fmerge_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] = [] ++ [EoCases.__re_concat_merge.case_0 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1
  group_step with case_1_eo__24re_5fconcat_5fmerge_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] = [EoCases.__re_concat_merge.case_0 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_1 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hl_0
  group_step with case_2_eo__24re_5fconcat_5fmerge_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] = [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_2 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hl_0 hl_1
  group_step with case_3_eo__24re_5fconcat_5fmerge_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] = [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_3 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_concat_merge.case_4 x_a0 x_a1 = none ∧ EoCases.__re_concat_merge.case_5 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24re_5fconcat_5fmerge_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] = [] ++ [EoCases.__re_concat_merge.case_4 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_5 x_a0 x_a1] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1
  group_step with case_5_eo__24re_5fconcat_5fmerge_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] = [EoCases.__re_concat_merge.case_4 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_5 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__re_concat_merge` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24re_5fconcat_5fmerge.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __re_concat_merge x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1, EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __re_concat_merge
  unfold EoCases.__re_concat_merge.case_0 EoCases.__re_concat_merge.case_1 EoCases.__re_concat_merge.case_2 EoCases.__re_concat_merge.case_3 EoCases.__re_concat_merge.case_4 EoCases.__re_concat_merge.case_5
  logos_eq

theorem body_eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24re_5fconcat_5fmerge s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_concat_merge x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24re_5fconcat_5fmerge.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24re_5fconcat_5fmerge
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  body_group_step with cases_0_0_eo__24re_5fconcat_5fmerge_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1, EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] = [] ++ [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1
  body_group_step with cases_0_1_eo__24re_5fconcat_5fmerge_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1, EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] = [EoCases.__re_concat_merge.case_0 x_a0 x_a1, EoCases.__re_concat_merge.case_1 x_a0 x_a1, EoCases.__re_concat_merge.case_2 x_a0 x_a1, EoCases.__re_concat_merge.case_3 x_a0 x_a1] ++ [EoCases.__re_concat_merge.case_4 x_a0 x_a1, EoCases.__re_concat_merge.case_5 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__re_concat_merge.case_0 EoCases.__re_concat_merge.case_1 EoCases.__re_concat_merge.case_2 EoCases.__re_concat_merge.case_3 EoCases.__re_concat_merge.case_4 EoCases.__re_concat_merge.case_5

theorem eo__24re_5fconcat_5fmerge_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24re_5fconcat_5fmerge.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24re_5fconcat_5fmerge
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24re_5fconcat_5fmerge s1 a0 a1) (fun s' t => Represents.rep s' t (__re_concat_merge x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24re_5fconcat_5fmerge_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24re_5fis_5funbound_5fwildcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__re_is_unbound_wildcard.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__re_is_unbound_wildcard.case_0 x_a0 = some (__re_is_unbound_wildcard y0)
      | core.result.Result.Ok none => EoCases.__re_is_unbound_wildcard.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24re_5fis_5funbound_5fwildcard more_0_eo__24re_5fis_5funbound_5fwildcard
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_is_unbound_wildcard.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_is_unbound_wildcard.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_is_unbound_wildcard.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__re_is_unbound_wildcard.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__re_is_unbound_wildcard.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__re_is_unbound_wildcard.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__re_is_unbound_wildcard.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s2 e_v17 (by rw [he_v17]; exact empty_args) hinv2 h64 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v15 h_v16
  pat_same v15 v17 with h_v15 h_v17 using hinv3 else hinv3 hG in EoCases.__re_is_unbound_wildcard.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s3 e_v18 (by rw [he_v18]; exact empty_args) hinv3 h64 as ⟨v18, s4, hinv4, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v15 h_v16 h_v17
  pat_same v16 v18 with h_v16 h_v18 using hinv4 else hinv4 hG in EoCases.__re_is_unbound_wildcard.case_0
  pat_unapply h_v13 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv4 else hinv4 hG in EoCases.__re_is_unbound_wildcard.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s4 e_v22 (by rw [he_v22]; exact empty_args) hinv4 h64 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v15 h_v16 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv5 else hinv5 hG in EoCases.__re_is_unbound_wildcard.case_0
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s5 _ _ rfl hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v15 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22
  pat_same v21 v23 with h_v21 h_v23 using hinv6 else hinv6 hG in EoCases.__re_is_unbound_wildcard.case_0
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v12 h_v13 h_v15 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23
  case_done hinv7 hG with h_v24 in EoCases.__re_is_unbound_wildcard.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v12 hn_v13 hn_v15 hn_v16 hn_v20 hn_v21

theorem case_1_eo__24re_5fis_5funbound_5fwildcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__re_is_unbound_wildcard.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__re_is_unbound_wildcard.case_1 x_a0 = some (__re_is_unbound_wildcard y0)
      | core.result.Result.Ok none => EoCases.__re_is_unbound_wildcard.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24re_5fis_5funbound_5fwildcard
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_is_unbound_wildcard.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_is_unbound_wildcard.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_is_unbound_wildcard.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__re_is_unbound_wildcard.case_1
  case_again hinv2 hG with h_v2 in EoCases.__re_is_unbound_wildcard.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24re_5fis_5funbound_5fwildcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__re_is_unbound_wildcard.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__re_is_unbound_wildcard.case_2 x_a0 = some (__re_is_unbound_wildcard y0)
      | core.result.Result.Ok none => EoCases.__re_is_unbound_wildcard.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24re_5fis_5funbound_5fwildcard
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__re_is_unbound_wildcard.case_2 using hn_a0

/-- logos's `__re_is_unbound_wildcard` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24re_5fis_5funbound_5fwildcard.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __re_is_unbound_wildcard x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__re_is_unbound_wildcard.case_0 x_a0, EoCases.__re_is_unbound_wildcard.case_1 x_a0, EoCases.__re_is_unbound_wildcard.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __re_is_unbound_wildcard
  unfold EoCases.__re_is_unbound_wildcard.case_0 EoCases.__re_is_unbound_wildcard.case_1 EoCases.__re_is_unbound_wildcard.case_2
  logos_eq

theorem step_eo__24re_5fis_5funbound_5fwildcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__re_is_unbound_wildcard x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __re_is_unbound_wildcard x_a0 = __re_is_unbound_wildcard y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24re_5fis_5funbound_5fwildcard.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24re_5fis_5funbound_5fwildcard
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  round_step with case_0_eo__24re_5fis_5funbound_5fwildcard_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using hn_a0
  round_step with case_1_eo__24re_5fis_5funbound_5fwildcard_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hn_a0 hc0
  round_step with case_2_eo__24re_5fis_5funbound_5fwildcard_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hn_a0 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hc0 hc1 hc2 in EoCases.__re_is_unbound_wildcard.case_0 EoCases.__re_is_unbound_wildcard.case_1 EoCases.__re_is_unbound_wildcard.case_2

theorem body_eo__24re_5fis_5funbound_5fwildcard_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_is_unbound_wildcard x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24re_5fis_5funbound_5fwildcard s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_is_unbound_wildcard x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24re_5fis_5funbound_5fwildcard body_eo__24re_5fis_5funbound_5fwildcard_loop
  step with step_eo__24re_5fis_5funbound_5fwildcard_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24re_5fis_5funbound_5fwildcard at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24re_5fis_5funbound_5fwildcard_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24re_5fis_5funbound_5fwildcard.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24re_5fis_5funbound_5fwildcard
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 965#u32 _ [a0] rfl
    (fun s1 => body_eo__24re_5fis_5funbound_5fwildcard s1 a0) (fun s' t => Represents.rep s' t (__re_is_unbound_wildcard x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_965 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_965 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24re_5fis_5funbound_5fwildcard_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eall.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__re_nullable.case_0 using hn_a0

theorem case_1_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_1
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__re_nullable.case_1 using hn_a0

theorem case_2_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_2
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__re_nullable.case_2 using hn_a0

theorem case_3_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_3
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_3
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_is_str s1 e_v4 (by rw [he_v4]; rfl) h_v2 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  have h_req_v8 := (show requires_0_eo__24re_5fnullable s3 v4 v5 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24re_5fnullable
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v4 v5 with h_v4 h_v5 using hinv3 hG
    req_stuck h_v4 as hq_v4 using hinv3 hG
    try simp only [eostring.EoString.from_code_points, Std.bind_ok]
    store_step with Store.literal_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
    step as ⟨e_v7, he_v7⟩
    store_step with Store.builtin_spec_eq s4 e_v7 (by rw [he_v7]; rfl) h_v2 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
    req_done hinv5 hG with h_v7 using hq_v4)
  store_step with h_req_v8 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv6 hG with h_v8 in EoCases.__re_nullable.case_3 using hn_a0 hn_v1 hn_v2

theorem case_4_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_4
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__re_nullable.case_4 using hn_a0 hn_v1 hn_v2

theorem case_5_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_5
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_nullable.case_5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2erange.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_5
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv2 hG with h_v7 in EoCases.__re_nullable.case_5 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_6_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_6_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_6
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_nullable.case_6
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_6
  store_step with ih.eo__24re_5fnullable s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24re_5fnullable s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_or s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__re_nullable.case_6 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_7_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_7_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_7
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_nullable.case_7
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_7
  store_step with ih.eo__24re_5fnullable s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24re_5fnullable s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_and s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__re_nullable.case_7 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_8_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_8_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_8
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_nullable.case_8
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_8
  store_step with ih.eo__24re_5fnullable s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24re_5fnullable s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_and s3 e_v9 (by rw [he_v9]; rfl) h_v7 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv4 hG with h_v9 in EoCases.__re_nullable.case_8 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_9_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_9_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_nullable.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_nullable.case_9
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_nullable.case_9
  store_step with ih.eo__24re_5fnullable s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_not s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__re_nullable.case_9 using hn_a0 hn_v1 hn_v2

theorem cases_0_0_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_0 x_a0 = none ∧ EoCases.__re_nullable.case_1 x_a0 = none ∧ EoCases.__re_nullable.case_2 x_a0 = none ∧ EoCases.__re_nullable.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24re_5fnullable_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] = [] ++ [EoCases.__re_nullable.case_0 x_a0] ++ [EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24re_5fnullable_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] = [EoCases.__re_nullable.case_0 x_a0] ++ [EoCases.__re_nullable.case_1 x_a0] ++ [EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24re_5fnullable_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] = [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0] ++ [EoCases.__re_nullable.case_2 x_a0] ++ [EoCases.__re_nullable.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24re_5fnullable_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] = [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0] ++ [EoCases.__re_nullable.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_4 x_a0 = none ∧ EoCases.__re_nullable.case_5 x_a0 = none ∧ EoCases.__re_nullable.case_6 x_a0 = none ∧ EoCases.__re_nullable.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24re_5fnullable_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] = [] ++ [EoCases.__re_nullable.case_4 x_a0] ++ [EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24re_5fnullable_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] = [EoCases.__re_nullable.case_4 x_a0] ++ [EoCases.__re_nullable.case_5 x_a0] ++ [EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_step with case_6_eo__24re_5fnullable_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] = [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0] ++ [EoCases.__re_nullable.case_6 x_a0] ++ [EoCases.__re_nullable.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hl_4 hl_5
  group_step with case_7_eo__24re_5fnullable_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] = [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0] ++ [EoCases.__re_nullable.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_nullable.case_8 x_a0 = none ∧ EoCases.__re_nullable.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24re_5fnullable_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] = [] ++ [EoCases.__re_nullable.case_8 x_a0] ++ [EoCases.__re_nullable.case_9 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0
  group_step with case_9_eo__24re_5fnullable_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] = [EoCases.__re_nullable.case_8 x_a0] ++ [EoCases.__re_nullable.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hl_8
  group_none hinv2 hG with ⟨hl_8, hl_9⟩

/-- logos's `__re_nullable` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24re_5fnullable.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __re_nullable x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0, EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0, EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __re_nullable
  unfold EoCases.__re_nullable.case_0 EoCases.__re_nullable.case_1 EoCases.__re_nullable.case_2 EoCases.__re_nullable.case_3 EoCases.__re_nullable.case_4 EoCases.__re_nullable.case_5 EoCases.__re_nullable.case_6 EoCases.__re_nullable.case_7 EoCases.__re_nullable.case_8 EoCases.__re_nullable.case_9
  logos_eq

theorem body_eo__24re_5fnullable_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24re_5fnullable s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_nullable x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24re_5fnullable.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24re_5fnullable
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_0_0_eo__24re_5fnullable_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0, EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0, EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] = [] ++ [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] ++ [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0, EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  body_group_step with cases_0_1_eo__24re_5fnullable_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0, EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0, EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] = [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0] ++ [EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] ++ [EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24re_5fnullable_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0, EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0, EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] = [EoCases.__re_nullable.case_0 x_a0, EoCases.__re_nullable.case_1 x_a0, EoCases.__re_nullable.case_2 x_a0, EoCases.__re_nullable.case_3 x_a0, EoCases.__re_nullable.case_4 x_a0, EoCases.__re_nullable.case_5 x_a0, EoCases.__re_nullable.case_6 x_a0, EoCases.__re_nullable.case_7 x_a0] ++ [EoCases.__re_nullable.case_8 x_a0, EoCases.__re_nullable.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_8, hl_9⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 in EoCases.__re_nullable.case_0 EoCases.__re_nullable.case_1 EoCases.__re_nullable.case_2 EoCases.__re_nullable.case_3 EoCases.__re_nullable.case_4 EoCases.__re_nullable.case_5 EoCases.__re_nullable.case_6 EoCases.__re_nullable.case_7 EoCases.__re_nullable.case_8 EoCases.__re_nullable.case_9

theorem eo__24re_5fnullable_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24re_5fnullable.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24re_5fnullable
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 966#u32 _ [a0] rfl
    (fun s1 => body_eo__24re_5fnullable s1 a0) (fun s' t => Represents.rep s' t (__re_nullable x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_966 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_966 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24re_5fnullable_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_rev_comp.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eall.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__re_rev_comp.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2eall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__re_rev_comp.case_0 using hn_a0

theorem case_1_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_rev_comp.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2enone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__re_rev_comp.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2enone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__re_rev_comp.case_1 using hn_a0

theorem case_2_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_rev_comp.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_rev_comp.case_2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_rev_comp.case_2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s4 v5 v6 _ _ hinv4 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24re_5frev_5fmap_5frev s5 v2 v7 _ _ hinv5 h64 (hG.rem hrem) h_v2 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_mk_rep s6 v4 v8 _ _ hinv6 h64 h_v4 h_v8 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv7 hG with h_v9 in EoCases.__re_rev_comp.case_2 using hn_a0 hn_v1 hn_v2

theorem case_3_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_rev_comp.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_rev_comp.case_3
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_rev_comp.case_3
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_rev_comp.case_3
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2einter.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24re_5frev_5fmap_5frev s5 v5 v10 _ _ hinv5 h64 (hG.rem hrem) h_v5 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v7 v11 _ _ hinv6 h64 h_v7 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24re_5frev_5fcomp s7 v2 _ hinv7 h64 (hG.rem hrem) h_v2 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_mk_rep s8 v12 v13 _ _ hinv8 h64 h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv9 hG with h_v14 in EoCases.__re_rev_comp.case_3 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_4_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_rev_comp.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_rev_comp.case_4
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_rev_comp.case_4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_rev_comp.case_4
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2eunion.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24re_5frev_5fmap_5frev s5 v5 v10 _ _ hinv5 h64 (hG.rem hrem) h_v5 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v7 v11 _ _ hinv6 h64 h_v7 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24re_5frev_5fcomp s7 v2 _ hinv7 h64 (hG.rem hrem) h_v2 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_mk_rep s8 v12 v13 _ _ hinv8 h64 h_v12 h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  case_done hinv9 hG with h_v14 in EoCases.__re_rev_comp.case_4 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_5_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_rev_comp.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  case_done hinv hG with h_a0 in EoCases.__re_rev_comp.case_5 using hn_a0

theorem cases_0_0_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_0 x_a0 = none ∧ EoCases.__re_rev_comp.case_1 x_a0 = none ∧ EoCases.__re_rev_comp.case_2 x_a0 = none ∧ EoCases.__re_rev_comp.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24re_5frev_5fcomp_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] = [] ++ [EoCases.__re_rev_comp.case_0 x_a0] ++ [EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24re_5frev_5fcomp_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] = [EoCases.__re_rev_comp.case_0 x_a0] ++ [EoCases.__re_rev_comp.case_1 x_a0] ++ [EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24re_5frev_5fcomp_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] = [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0] ++ [EoCases.__re_rev_comp.case_2 x_a0] ++ [EoCases.__re_rev_comp.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24re_5frev_5fcomp_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] = [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0] ++ [EoCases.__re_rev_comp.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_rev_comp.case_4 x_a0 = none ∧ EoCases.__re_rev_comp.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24re_5frev_5fcomp_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] = [] ++ [EoCases.__re_rev_comp.case_4 x_a0] ++ [EoCases.__re_rev_comp.case_5 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24re_5frev_5fcomp_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] = [EoCases.__re_rev_comp.case_4 x_a0] ++ [EoCases.__re_rev_comp.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__re_rev_comp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24re_5frev_5fcomp.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __re_rev_comp x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0, EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __re_rev_comp
  unfold EoCases.__re_rev_comp.case_0 EoCases.__re_rev_comp.case_1 EoCases.__re_rev_comp.case_2 EoCases.__re_rev_comp.case_3 EoCases.__re_rev_comp.case_4 EoCases.__re_rev_comp.case_5
  logos_eq

theorem body_eo__24re_5frev_5fcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24re_5frev_5fcomp s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_rev_comp x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24re_5frev_5fcomp.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24re_5frev_5fcomp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_0_0_eo__24re_5frev_5fcomp_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0, EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] = [] ++ [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] ++ [EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  body_group_step with cases_0_1_eo__24re_5frev_5fcomp_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0, EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] = [EoCases.__re_rev_comp.case_0 x_a0, EoCases.__re_rev_comp.case_1 x_a0, EoCases.__re_rev_comp.case_2 x_a0, EoCases.__re_rev_comp.case_3 x_a0] ++ [EoCases.__re_rev_comp.case_4 x_a0, EoCases.__re_rev_comp.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__re_rev_comp.case_0 EoCases.__re_rev_comp.case_1 EoCases.__re_rev_comp.case_2 EoCases.__re_rev_comp.case_3 EoCases.__re_rev_comp.case_4 EoCases.__re_rev_comp.case_5

theorem eo__24re_5frev_5fcomp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24re_5frev_5fcomp.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24re_5frev_5fcomp
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 967#u32 _ [a0] rfl
    (fun s1 => body_eo__24re_5frev_5fcomp s1 a0) (fun s' t => Represents.rep s' t (__re_rev_comp x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_967 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_967 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24re_5frev_5fcomp_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24re_5frev_5fmap_5frev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24re_5frev_5fmap_5frev s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__re_rev_map_rev.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__re_rev_map_rev.case_0 x_a0 x_a1 = some (__re_rev_map_rev y0 y1)
      | core.result.Result.Ok none => EoCases.__re_rev_map_rev.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24re_5frev_5fmap_5frev
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_rev_map_rev.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__re_rev_map_rev.case_0
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s1 _ _ rfl hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__re_rev_map_rev.case_0
  case_done hinv2 hG with h_a1 in EoCases.__re_rev_map_rev.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24re_5frev_5fmap_5frev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24re_5frev_5fmap_5frev s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__re_rev_map_rev.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__re_rev_map_rev.case_1 x_a0 x_a1 = some (__re_rev_map_rev y0 y1)
      | core.result.Result.Ok none => EoCases.__re_rev_map_rev.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24re_5frev_5fmap_5frev
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_rev_map_rev.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_rev_map_rev.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_rev_map_rev.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24re_5frev_5fcomp s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_mk_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_mk_rep s4 v9 a1 _ _ hinv4 h64 h_v9 h_a1 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_again hinv5 hG with h_v2 h_v10 in EoCases.__re_rev_map_rev.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__re_rev_map_rev` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24re_5frev_5fmap_5frev.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __re_rev_map_rev x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__re_rev_map_rev.case_0 x_a0 x_a1, EoCases.__re_rev_map_rev.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __re_rev_map_rev
  unfold EoCases.__re_rev_map_rev.case_0 EoCases.__re_rev_map_rev.case_1
  logos_eq

theorem step_eo__24re_5frev_5fmap_5frev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24re_5frev_5fmap_5frev s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__re_rev_map_rev x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __re_rev_map_rev x_a0 x_a1 = __re_rev_map_rev y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24re_5frev_5fmap_5frev.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24re_5frev_5fmap_5frev
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24re_5frev_5fmap_5frev_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24re_5frev_5fmap_5frev_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__re_rev_map_rev.case_0 EoCases.__re_rev_map_rev.case_1

theorem body_eo__24re_5frev_5fmap_5frev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24re_5frev_5fmap_5frev s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_rev_map_rev x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24re_5frev_5fmap_5frev s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_rev_map_rev x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24re_5frev_5fmap_5frev body_eo__24re_5frev_5fmap_5frev_loop
  step with step_eo__24re_5frev_5fmap_5frev_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24re_5frev_5fmap_5frev at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24re_5frev_5fmap_5frev_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24re_5frev_5fmap_5frev.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24re_5frev_5fmap_5frev
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 968#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24re_5frev_5fmap_5frev s1 a0 a1) (fun s' t => Represents.rep s' t (__re_rev_map_rev x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_968 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_968 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24re_5frev_5fmap_5frev_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24re_5fsplit_5fstr_5fto_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24re_5fsplit_5fstr_5fto_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_split_str_to_re.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_split_str_to_re.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24re_5fsplit_5fstr_5fto_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__re_split_str_to_re.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__re_split_str_to_re.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__re_split_str_to_re.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24re_5fsplit_5fstr_5fto_5fre s5 v2 a1 _ _ hinv5 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__re_split_str_to_re.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24re_5fsplit_5fstr_5fto_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24re_5fsplit_5fstr_5fto_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__re_split_str_to_re.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__re_split_str_to_re.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24re_5fsplit_5fstr_5fto_5fre
  have hG := Store.Grows.refl s
  case_done hinv hG with h_a1 in EoCases.__re_split_str_to_re.case_1 using hn_a0 hn_a1

/-- logos's `__re_split_str_to_re` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24re_5fsplit_5fstr_5fto_5fre.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __re_split_str_to_re x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__re_split_str_to_re.case_0 x_a0 x_a1, EoCases.__re_split_str_to_re.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __re_split_str_to_re
  unfold EoCases.__re_split_str_to_re.case_0 EoCases.__re_split_str_to_re.case_1
  logos_eq

theorem body_eo__24re_5fsplit_5fstr_5fto_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24re_5fsplit_5fstr_5fto_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__re_split_str_to_re x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24re_5fsplit_5fstr_5fto_5fre.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24re_5fsplit_5fstr_5fto_5fre
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24re_5fsplit_5fstr_5fto_5fre_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24re_5fsplit_5fstr_5fto_5fre_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__re_split_str_to_re.case_0 EoCases.__re_split_str_to_re.case_1

theorem eo__24re_5fsplit_5fstr_5fto_5fre_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24re_5fsplit_5fstr_5fto_5fre.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24re_5fsplit_5fstr_5fto_5fre
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 969#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24re_5fsplit_5fstr_5fto_5fre s1 a0 a1) (fun s' t => Represents.rep s' t (__re_split_str_to_re x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_969 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_969 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24re_5fsplit_5fstr_5fto_5fre_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
