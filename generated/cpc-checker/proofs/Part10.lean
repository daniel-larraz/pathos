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

theorem case_0_eo__24run_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24run_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__run_process_scope.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__run_process_scope.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24run_5fprocess_5fscope
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__run_process_scope.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_not.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with ih.eo__24extract_5fantec s3 a0 v2 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_mk_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__run_process_scope.case_0 using hn_a0 hn_a1

theorem case_1_eo__24run_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24run_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__run_process_scope.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__run_process_scope.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24run_5fprocess_5fscope
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24extract_5fantec s1 a0 a1 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_mk_rep s2 v0 v1 _ _ hinv2 h64 h_v0 h_v1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_mk_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__run_process_scope.case_1 using hn_a0 hn_a1

/-- logos's `__run_process_scope` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24run_5fprocess_5fscope.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __run_process_scope x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__run_process_scope.case_0 x_a0 x_a1, EoCases.__run_process_scope.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __run_process_scope
  unfold EoCases.__run_process_scope.case_0 EoCases.__run_process_scope.case_1
  logos_eq

theorem body_eo__24run_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24run_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__run_process_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24run_5fprocess_5fscope.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24run_5fprocess_5fscope
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24run_5fprocess_5fscope_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24run_5fprocess_5fscope_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__run_process_scope.case_0 EoCases.__run_process_scope.case_1

theorem eo__24run_5fprocess_5fscope_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24run_5fprocess_5fscope.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24run_5fprocess_5fscope
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24run_5fprocess_5fscope s1 a0 a1) (fun s' t => Represents.rep s' t (__run_process_scope x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24run_5fprocess_5fscope_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24seq_5felement_5fof_5funit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24seq_5felement_5fof_5funit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__seq_element_of_unit.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__seq_element_of_unit.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24seq_5felement_5fof_5funit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__seq_element_of_unit.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__seq_element_of_unit.case_0
  case_done hinv1 hG with h_v2 in EoCases.__seq_element_of_unit.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__seq_element_of_unit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24seq_5felement_5fof_5funit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __seq_element_of_unit x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__seq_element_of_unit.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __seq_element_of_unit
  unfold EoCases.__seq_element_of_unit.case_0
  logos_eq

theorem body_eo__24seq_5felement_5fof_5funit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24seq_5felement_5fof_5funit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__seq_element_of_unit x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24seq_5felement_5fof_5funit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24seq_5felement_5fof_5funit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24seq_5felement_5fof_5funit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__seq_element_of_unit.case_0

theorem eo__24seq_5felement_5fof_5funit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24seq_5felement_5fof_5funit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24seq_5felement_5fof_5funit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24seq_5felement_5fof_5funit s1 a0) (fun s' t => Represents.rep s' t (__seq_element_of_unit x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24seq_5felement_5fof_5funit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24seq_5fis_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24seq_5fis_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__seq_is_non_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__seq_is_non_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24seq_5fis_5fnon_5fempty
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__seq_is_non_empty.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__seq_is_non_empty.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__seq_is_non_empty.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__seq_is_non_empty.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__seq_is_non_empty.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10
  case_done hinv3 hG with h_v11 in EoCases.__seq_is_non_empty.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

theorem case_1_eo__24seq_5fis_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24seq_5fis_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__seq_is_non_empty.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__seq_is_non_empty.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24seq_5fis_5fnon_5fempty
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__seq_is_non_empty.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__seq_is_non_empty.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__seq_is_non_empty.case_1 using hn_a0 hn_v1 hn_v2

theorem case_2_eo__24seq_5fis_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24seq_5fis_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__seq_is_non_empty.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__seq_is_non_empty.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24seq_5fis_5fnon_5fempty
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__seq_is_non_empty.case_2 using hn_a0

/-- logos's `__seq_is_non_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24seq_5fis_5fnon_5fempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __seq_is_non_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__seq_is_non_empty.case_0 x_a0, EoCases.__seq_is_non_empty.case_1 x_a0, EoCases.__seq_is_non_empty.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __seq_is_non_empty
  unfold EoCases.__seq_is_non_empty.case_0 EoCases.__seq_is_non_empty.case_1 EoCases.__seq_is_non_empty.case_2
  logos_eq

theorem body_eo__24seq_5fis_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24seq_5fis_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__seq_is_non_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24seq_5fis_5fnon_5fempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24seq_5fis_5fnon_5fempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24seq_5fis_5fnon_5fempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24seq_5fis_5fnon_5fempty_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  case_step with case_2_eo__24seq_5fis_5fnon_5fempty_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hn_a0 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hc0 hc1 hc2 in EoCases.__seq_is_non_empty.case_0 EoCases.__seq_is_non_empty.case_1 EoCases.__seq_is_non_empty.case_2

theorem eo__24seq_5fis_5fnon_5fempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24seq_5fis_5fnon_5fempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24seq_5fis_5fnon_5fempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24seq_5fis_5fnon_5fempty s1 a0) (fun s' t => Represents.rep s' t (__seq_is_non_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24seq_5fis_5fnon_5fempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_has_dt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_has_dt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdd_5fhas_5fdt
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_dd_has_dt.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_or s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__smtx_dd_has_dt.case_0 using

theorem case_1_eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_has_dt.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_has_dt.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdd_5fhas_5fdt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dd_has_dt.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dd_has_dt.case_1 using

/-- logos's `__smtx_dd_has_dt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdd_5fhas_5fdt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dd_has_dt x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dd_has_dt.case_0 x_a0 x_a1, EoCases.__smtx_dd_has_dt.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dd_has_dt
  unfold EoCases.__smtx_dd_has_dt.case_0 EoCases.__smtx_dd_has_dt.case_1
  logos_eq

theorem body_eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdd_5fhas_5fdt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dd_has_dt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdd_5fhas_5fdt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdd_5fhas_5fdt
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdd_5fhas_5fdt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdd_5fhas_5fdt_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dd_has_dt.case_0 EoCases.__smtx_dd_has_dt.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdd_5fhas_5fdt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdd_5fhas_5fdt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdd_5fhas_5fdt
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 986#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdd_5fhas_5fdt s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dd_has_dt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_986 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_986 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdd_5fhas_5fdt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_lookup.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_lookup.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdd_5flookup
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_dd_lookup.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  have h_ite_v6 := (show if_0_eo__24smtx_5fdd_5flookup s1 v4 v2 a0 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5fdd_5flookup
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_v2)
    · ite_branch hbv_5
      store_step with ih.eo__24smtx_5fdd_5flookup s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__smtx_dd_lookup.case_0 using

theorem case_1_eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dd_lookup.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dd_lookup.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdd_5flookup
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dd_lookup.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dd_lookup.case_1 using

/-- logos's `__smtx_dd_lookup` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdd_5flookup.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dd_lookup x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dd_lookup.case_0 x_a0 x_a1, EoCases.__smtx_dd_lookup.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_dd_lookup
  unfold EoCases.__smtx_dd_lookup.case_0 EoCases.__smtx_dd_lookup.case_1
  logos_eq

theorem body_eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdd_5flookup.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdd_5flookup
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdd_5flookup_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdd_5flookup_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dd_lookup.case_0 EoCases.__smtx_dd_lookup.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdd_5flookup_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdd_5flookup.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdd_5flookup
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 987#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdd_5flookup s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dd_lookup x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_987 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_987 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdd_5flookup_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_inhabited.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_inhabited.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdecl_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_decl_inhabited.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  have h_ite_v7 := (show if_0_eo__24smtx_5fdecl_5finhabited s1 v4 v2 v3 a0 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5fdecl_5finhabited
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      store_step with ih.eo__24smtx_5fdt_5finhabited s1 v2 v3 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      store_step with ih.eo__24smtx_5fdecl_5finhabited s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v7 in EoCases.__smtx_decl_inhabited.case_0 using

theorem case_1_eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_inhabited.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_inhabited.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdecl_5finhabited
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_decl_inhabited.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_decl_inhabited.case_1 using

/-- logos's `__smtx_decl_inhabited` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdecl_5finhabited.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_decl_inhabited x_a0 x_a1 =
      (firstSome [EoCases.__smtx_decl_inhabited.case_0 x_a0 x_a1, EoCases.__smtx_decl_inhabited.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_decl_inhabited
  unfold EoCases.__smtx_decl_inhabited.case_0 EoCases.__smtx_decl_inhabited.case_1
  logos_eq

theorem body_eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdecl_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_decl_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdecl_5finhabited.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdecl_5finhabited
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdecl_5finhabited_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdecl_5finhabited_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_decl_inhabited.case_0 EoCases.__smtx_decl_inhabited.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdecl_5finhabited_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdecl_5finhabited.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdecl_5finhabited
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 988#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdecl_5finhabited s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_decl_inhabited x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_988 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_988 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdecl_5finhabited_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_wf_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_wf_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdecl_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_decl_wf_rec.case_0
  store_step with ih.eo__24smtx_5fdt_5fwf_5frec s a0 v2 _ _ hinv h64 hrem h_a0 h_v2 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 h_a0 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5finhabited_5ftype s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5fdecl_5fwf_5frec s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s4 v1 v3 _ _ hinv4 h64 (hG.rem hrem) h_v1 h_v3 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_not s5 e_v9 (by rw [he_v9]; rfl) h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.native_spec_and s6 e_v10 (by rw [he_v10]; rfl) h_v7 h_v9 hinv6 h64 as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.native_spec_and s7 e_v11 (by rw [he_v11]; rfl) h_v6 h_v10 hinv7 h64 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with Store.native_spec_and s8 e_v12 (by rw [he_v12]; rfl) h_v4 h_v11 hinv8 h64 as ⟨v12, s9, hinv9, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv9 hG with h_v12 in EoCases.__smtx_decl_wf_rec.case_0 using

theorem case_1_eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_decl_wf_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_decl_wf_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdecl_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_decl_wf_rec.case_1
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_decl_wf_rec.case_1 using

/-- logos's `__smtx_decl_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdecl_5fwf_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_decl_wf_rec x_a0 x_a1 =
      (firstSome [EoCases.__smtx_decl_wf_rec.case_0 x_a0 x_a1, EoCases.__smtx_decl_wf_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_decl_wf_rec
  unfold EoCases.__smtx_decl_wf_rec.case_0 EoCases.__smtx_decl_wf_rec.case_1
  logos_eq

theorem body_eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdecl_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_decl_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdecl_5fwf_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdecl_5fwf_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdecl_5fwf_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdecl_5fwf_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_decl_wf_rec.case_0 EoCases.__smtx_decl_wf_rec.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdecl_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdecl_5fwf_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdecl_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 989#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdecl_5fwf_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_decl_wf_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_989 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_989 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdecl_5fwf_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_inhabited.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_inhabited.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_inhabited.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__smtx_dt_cons_inhabited.case_0
  store_step with ih.eo__24smtx_5fdecl_5finhabited s v4 a1 _ _ hinv h64 hrem h_v4 h_a1 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24smtx_5fdt_5fcons_5finhabited s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__smtx_dt_cons_inhabited.case_0 using

theorem case_1_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_inhabited.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_inhabited.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_inhabited.case_1
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5fcons_5finhabited s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_cons_inhabited.case_1 using

theorem case_2_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_inhabited.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_inhabited.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_cons_inhabited.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_cons_inhabited.case_2 using

/-- logos's `__smtx_dt_cons_inhabited` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fcons_5finhabited.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_cons_inhabited x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_cons_inhabited.case_0 x_a0 x_a1, EoCases.__smtx_dt_cons_inhabited.case_1 x_a0 x_a1, EoCases.__smtx_dt_cons_inhabited.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_cons_inhabited
  unfold EoCases.__smtx_dt_cons_inhabited.case_0 EoCases.__smtx_dt_cons_inhabited.case_1 EoCases.__smtx_dt_cons_inhabited.case_2
  logos_eq

theorem body_eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fcons_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_cons_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fcons_5finhabited.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fcons_5finhabited
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fcons_5finhabited_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fcons_5finhabited_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5fdt_5fcons_5finhabited_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_dt_cons_inhabited.case_0 EoCases.__smtx_dt_cons_inhabited.case_1 EoCases.__smtx_dt_cons_inhabited.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fcons_5finhabited_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fcons_5finhabited.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fcons_5finhabited
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 990#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fcons_5finhabited s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_cons_inhabited x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_990 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_990 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fcons_5finhabited_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_wf_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_wf_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_wf_rec.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__smtx_dt_cons_wf_rec.case_0
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s v4 a0 _ _ hinv h64 hrem h_v4 h_a0 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s1 a0 v2 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__smtx_dt_cons_wf_rec.case_0 using

theorem case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_wf_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_wf_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_cons_wf_rec.case_1
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s3 a0 v2 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v7 in EoCases.__smtx_dt_cons_wf_rec.case_1 using

theorem case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_cons_wf_rec.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_cons_wf_rec.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_cons_wf_rec.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_cons_wf_rec.case_2 using

/-- logos's `__smtx_dt_cons_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fcons_5fwf_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_cons_wf_rec x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_cons_wf_rec.case_0 x_a0 x_a1, EoCases.__smtx_dt_cons_wf_rec.case_1 x_a0 x_a1, EoCases.__smtx_dt_cons_wf_rec.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_cons_wf_rec
  unfold EoCases.__smtx_dt_cons_wf_rec.case_0 EoCases.__smtx_dt_cons_wf_rec.case_1 EoCases.__smtx_dt_cons_wf_rec.case_2
  logos_eq

theorem body_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_cons_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fcons_5fwf_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fcons_5fwf_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_dt_cons_wf_rec.case_0 EoCases.__smtx_dt_cons_wf_rec.case_1 EoCases.__smtx_dt_cons_wf_rec.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fcons_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fcons_5fwf_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fcons_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 991#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fcons_5fwf_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_cons_wf_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_991 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_991 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fcons_5fwf_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_inhabited.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_inhabited.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5finhabited
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_inhabited.case_0
  store_step with ih.eo__24smtx_5fdt_5fcons_5finhabited s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5finhabited s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_or s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_inhabited.case_0 using

theorem case_1_eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_inhabited.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_inhabited.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5finhabited
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_inhabited.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_inhabited.case_1 using

/-- logos's `__smtx_dt_inhabited` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5finhabited.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_inhabited x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_inhabited.case_0 x_a0 x_a1, EoCases.__smtx_dt_inhabited.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_inhabited
  unfold EoCases.__smtx_dt_inhabited.case_0 EoCases.__smtx_dt_inhabited.case_1
  logos_eq

theorem body_eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5finhabited s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_inhabited x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5finhabited.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5finhabited
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5finhabited_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5finhabited_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dt_inhabited.case_0 EoCases.__smtx_dt_inhabited.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5finhabited_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5finhabited.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5finhabited
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 992#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5finhabited s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_inhabited x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_992 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_992 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5finhabited_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_resolve.case_0
  store_step with ih.eo__24smtx_5fdtc_5fresolve s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_resolve.case_0 using

theorem case_1_eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_resolve.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_resolve.case_1 using

/-- logos's `__smtx_dt_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_resolve x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_resolve.case_0 x_a0 x_a1, EoCases.__smtx_dt_resolve.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_dt_resolve
  unfold EoCases.__smtx_dt_resolve.case_0 EoCases.__smtx_dt_resolve.case_1
  logos_eq

theorem body_eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dt_resolve.case_0 EoCases.__smtx_dt_resolve.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 994#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_994 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_994 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_wf_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_wf_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdt_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dt_wf_rec.case_0
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s a0 v1 _ _ hinv h64 hrem h_a0 h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdt_5fwf_5frec s1 a0 v2 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_dt_wf_rec.case_0 using

theorem case_1_eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dt_wf_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dt_wf_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdt_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dt_wf_rec.case_1
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dt_wf_rec.case_1 using

/-- logos's `__smtx_dt_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdt_5fwf_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dt_wf_rec x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dt_wf_rec.case_0 x_a0 x_a1, EoCases.__smtx_dt_wf_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_dt_wf_rec
  unfold EoCases.__smtx_dt_wf_rec.case_0 EoCases.__smtx_dt_wf_rec.case_1
  logos_eq

theorem body_eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdt_5fwf_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dt_wf_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdt_5fwf_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdt_5fwf_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdt_5fwf_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdt_5fwf_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dt_wf_rec.case_0 EoCases.__smtx_dt_wf_rec.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5fdt_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdt_5fwf_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdt_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 995#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdt_5fwf_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dt_wf_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_995 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_995 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdt_5fwf_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdtc_5fnum_5fsels_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5fdtc_5fnum_5fsels s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_num_sels.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_num_sels.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdtc_5fnum_5fsels
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dtc_num_sels.case_0
  store_step with ih.eo__24smtx_5fdtc_5fnum_5fsels s v2 _ hinv h64 hrem h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_nat_succ s1 e_v4 (by rw [he_v4]; rfl) h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_dtc_num_sels.case_0 using

theorem case_1_eo__24smtx_5fdtc_5fnum_5fsels_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5fdtc_5fnum_5fsels s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_num_sels.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_num_sels.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdtc_5fnum_5fsels
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dtc_num_sels.case_1
  store_step with Store.native_nat_zero_spec s1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dtc_num_sels.case_1 using

/-- logos's `__smtx_dtc_num_sels` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdtc_5fnum_5fsels.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_dtc_num_sels x_a0 =
      (firstSome [EoCases.__smtx_dtc_num_sels.case_0 x_a0, EoCases.__smtx_dtc_num_sels.case_1 x_a0] default) := by
  conv => lhs; unfold __smtx_dtc_num_sels
  unfold EoCases.__smtx_dtc_num_sels.case_0 EoCases.__smtx_dtc_num_sels.case_1
  logos_eq

theorem body_eo__24smtx_5fdtc_5fnum_5fsels_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5fdtc_5fnum_5fsels s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dtc_num_sels x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdtc_5fnum_5fsels.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5fdtc_5fnum_5fsels
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdtc_5fnum_5fsels_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24smtx_5fdtc_5fnum_5fsels_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_dtc_num_sels.case_0 EoCases.__smtx_dtc_num_sels.case_1 splitting x_a0

theorem eo__24smtx_5fdtc_5fnum_5fsels_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdtc_5fnum_5fsels.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5fdtc_5fnum_5fsels
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 996#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5fdtc_5fnum_5fsels s1 a0) (fun s' t => Represents.rep s' t (__smtx_dtc_num_sels x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_996 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_996 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdtc_5fnum_5fsels_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dtc_resolve.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__smtx_dtc_resolve.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24smtx_5fdtc_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__smtx_dtc_resolve.case_0 using

theorem case_1_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_dtc_resolve.case_1
  store_step with ih.eo__24smtx_5fdtc_5fresolve s v2 a1 _ _ hinv h64 hrem h_v2 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__smtx_dtc_resolve.case_1 using

theorem case_2_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_dtc_resolve.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_dtc_resolve.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_dtc_resolve.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_dtc_resolve.case_2 using

/-- logos's `__smtx_dtc_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fdtc_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_dtc_resolve x_a0 x_a1 =
      (firstSome [EoCases.__smtx_dtc_resolve.case_0 x_a0 x_a1, EoCases.__smtx_dtc_resolve.case_1 x_a0 x_a1, EoCases.__smtx_dtc_resolve.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_dtc_resolve
  unfold EoCases.__smtx_dtc_resolve.case_0 EoCases.__smtx_dtc_resolve.case_1 EoCases.__smtx_dtc_resolve.case_2
  logos_eq

theorem body_eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fdtc_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fdtc_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5fdtc_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5fdtc_5fresolve_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_dtc_resolve.case_0 EoCases.__smtx_dtc_resolve.case_1 EoCases.__smtx_dtc_resolve.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5fdtc_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fdtc_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5fdtc_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 997#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24smtx_5fdtc_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_dtc_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_997 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_997 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fdtc_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_0 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_inhabited_type.case_0
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_inhabited_type.case_0 using

theorem case_1_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_1 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_1
  case_again hinv hG with h_v2 in EoCases.__smtx_inhabited_type.case_1 using

theorem case_2_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_2 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_2
  store_step with ih.eo__24smtx_5fdecl_5finhabited s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_inhabited_type.case_2 using

theorem case_3_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_3 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_3
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_inhabited_type.case_3 using

theorem case_4_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_4 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_inhabited_type.case_4
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_inhabited_type.case_4 using

theorem case_5_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_inhabited_type.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          EoCases.__smtx_inhabited_type.case_5 x_a0 = some (__smtx_inhabited_type y0)
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_inhabited_type.case_5 using

theorem cases_0_0_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] d = __smtx_inhabited_type y0
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_0 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_1 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_2 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  group_round_step with case_0_eo__24smtx_5finhabited_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [] ++ [EoCases.__smtx_inhabited_type.case_0 x_a0] ++ [EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_round_step with case_1_eo__24smtx_5finhabited_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0] ++ [EoCases.__smtx_inhabited_type.case_1 x_a0] ++ [EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_round_step with case_2_eo__24smtx_5finhabited_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0] ++ [EoCases.__smtx_inhabited_type.case_2 x_a0] ++ [EoCases.__smtx_inhabited_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_round_step with case_3_eo__24smtx_5finhabited_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0] ++ [EoCases.__smtx_inhabited_type.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          ∀ d, firstSome [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] d = __smtx_inhabited_type y0
      | core.result.Result.Ok none => EoCases.__smtx_inhabited_type.case_4 x_a0 = none ∧ EoCases.__smtx_inhabited_type.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  group_round_step with case_4_eo__24smtx_5finhabited_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [] ++ [EoCases.__smtx_inhabited_type.case_4 x_a0] ++ [EoCases.__smtx_inhabited_type.case_5 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_round_step with case_5_eo__24smtx_5finhabited_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [EoCases.__smtx_inhabited_type.case_4 x_a0] ++ [EoCases.__smtx_inhabited_type.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__smtx_inhabited_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5finhabited_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_inhabited_type x_a0 =
      (firstSome [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0, EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_inhabited_type
  unfold EoCases.__smtx_inhabited_type.case_0 EoCases.__smtx_inhabited_type.case_1 EoCases.__smtx_inhabited_type.case_2 EoCases.__smtx_inhabited_type.case_3 EoCases.__smtx_inhabited_type.case_4 EoCases.__smtx_inhabited_type.case_5
  logos_eq

theorem step_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    step_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧
          __smtx_inhabited_type x_a0 = __smtx_inhabited_type y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5finhabited_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24smtx_5finhabited_5ftype
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  body_group_round_step with cases_0_0_eo__24smtx_5finhabited_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0, EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [] ++ [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] ++ [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_round_step with cases_0_1_eo__24smtx_5finhabited_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 hbud
    split (show [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0, EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] = [EoCases.__smtx_inhabited_type.case_0 x_a0, EoCases.__smtx_inhabited_type.case_1 x_a0, EoCases.__smtx_inhabited_type.case_2 x_a0, EoCases.__smtx_inhabited_type.case_3 x_a0] ++ [EoCases.__smtx_inhabited_type.case_4 x_a0, EoCases.__smtx_inhabited_type.case_5 x_a0] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hl_0 hl_1 hl_2 hl_3
  round_stuck hinv3 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__smtx_inhabited_type.case_0 EoCases.__smtx_inhabited_type.case_1 EoCases.__smtx_inhabited_type.case_2 EoCases.__smtx_inhabited_type.case_3 EoCases.__smtx_inhabited_type.case_4 EoCases.__smtx_inhabited_type.case_5 splitting x_a0

theorem body_eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 →
      body_eo__24smtx_5finhabited_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_inhabited_type x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0
  unfold body_eo__24smtx_5finhabited_5ftype body_eo__24smtx_5finhabited_5ftype_loop
  step with step_eo__24smtx_5finhabited_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24smtx_5finhabited_5ftype at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5finhabited_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5finhabited_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5finhabited_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 998#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5finhabited_5ftype s1 a0) (fun s' t => Represents.rep s' t (__smtx_inhabited_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_998 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_998 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5finhabited_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fret_5ftypeof_5fsel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_0_eo__24smtx_5fret_5ftypeof_5fsel s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fret_5ftypeof_5fsel
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5fdd_5flookup s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  store_step with ih.eo__24smtx_5fdt_5fresolve s1 v0 a1 _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  store_step with ih.eo__24smtx_5fret_5ftypeof_5fsel_5frec s2 v1 a2 a3 _ _ _ hinv2 h64 (hG.rem hrem) h_v1 h_a2 h_a3 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__smtx_ret_typeof_sel.case_0 using

/-- logos's `__smtx_ret_typeof_sel` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fret_5ftypeof_5fsel.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3 =
      (firstSome [EoCases.__smtx_ret_typeof_sel.case_0 x_a0 x_a1 x_a2 x_a3] default) := by
  conv => lhs; unfold __smtx_ret_typeof_sel
  unfold EoCases.__smtx_ret_typeof_sel.case_0
  logos_eq

theorem body_eo__24smtx_5fret_5ftypeof_5fsel_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24smtx_5fret_5ftypeof_5fsel s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fret_5ftypeof_5fsel.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24smtx_5fret_5ftypeof_5fsel
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5fret_5ftypeof_5fsel_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_ret_typeof_sel.case_0 splitting x_a0 x_a1 x_a2 x_a3

theorem eo__24smtx_5fret_5ftypeof_5fsel_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fret_5ftypeof_5fsel.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24smtx_5fret_5ftypeof_5fsel
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5fret_5ftypeof_5fsel s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__smtx_ret_typeof_sel x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fret_5ftypeof_5fsel_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_0
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s1 a2 h_a2 hinv1 h64 storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_0
  case_done hinv2 hG with h_v4 in EoCases.__smtx_ret_typeof_sel_rec.case_0 using

theorem case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_1
  pat_destruct CtorSpec.eo__24emb_5fdtc_2econs.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_1
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_1
  pat_destruct_lit Store.native_pattern_succ_spec s1 a2 h_a2 hinv1 h64 as ⟨v8, x_v8, h_v8⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 in EoCases.__smtx_ret_typeof_sel_rec.case_1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s2 e_v9 (by rw [he_v9]; rfl) h_v5 h_v2 hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v8
  store_step with Store.native_nat_zero_spec s3 hinv3 h64 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v8 h_v9
  case_again hinv4 hG with h_v9 h_v10 h_v8 in EoCases.__smtx_ret_typeof_sel_rec.case_1 using

theorem case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_ret_typeof_sel_rec.case_2
  pat_destruct_lit Store.native_pattern_succ_spec s a1 h_a1 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__smtx_ret_typeof_sel_rec.case_2
  case_again hinv1 hG with h_v2 h_v4 h_a2 in EoCases.__smtx_ret_typeof_sel_rec.case_2 using

theorem case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2 = some (__smtx_ret_typeof_sel_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_ret_typeof_sel_rec.case_3 using

/-- logos's `__smtx_ret_typeof_sel_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5fret_5ftypeof_5fsel_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_ret_typeof_sel_rec.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_ret_typeof_sel_rec.case_1 x_a0 x_a1 x_a2, EoCases.__smtx_ret_typeof_sel_rec.case_2 x_a0 x_a1 x_a2, EoCases.__smtx_ret_typeof_sel_rec.case_3 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_ret_typeof_sel_rec
  unfold EoCases.__smtx_ret_typeof_sel_rec.case_0 EoCases.__smtx_ret_typeof_sel_rec.case_1 EoCases.__smtx_ret_typeof_sel_rec.case_2 EoCases.__smtx_ret_typeof_sel_rec.case_3
  logos_eq

theorem step_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2 = __smtx_ret_typeof_sel_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5fret_5ftypeof_5fsel_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24smtx_5fret_5ftypeof_5fsel_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_step with case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s4 a0 a1 a2 x_a0 x_a1 x_a2 hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__smtx_ret_typeof_sel_rec.case_0 EoCases.__smtx_ret_typeof_sel_rec.case_1 EoCases.__smtx_ret_typeof_sel_rec.case_2 EoCases.__smtx_ret_typeof_sel_rec.case_3 splitting x_a0 x_a1 x_a2

theorem body_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24smtx_5fret_5ftypeof_5fsel_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24smtx_5fret_5ftypeof_5fsel_5frec body_eo__24smtx_5fret_5ftypeof_5fsel_5frec_loop
  step with step_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24smtx_5fret_5ftypeof_5fsel_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5fret_5ftypeof_5fsel_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5fret_5ftypeof_5fsel_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1000#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24smtx_5fret_5ftypeof_5fsel_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_ret_typeof_sel_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_1000 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1000 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5fret_5ftypeof_5fsel_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf.case_0
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf.case_0 using

theorem case_1_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf.case_1
  store_step with ih.eo__24smtx_5ftype_5fwf_5fcomponent s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_type_wf.case_1 using

theorem case_2_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5ftype_5fwf_5fcomponent s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_type_wf.case_2 using

/-- logos's `__smtx_type_wf` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf x_a0 =
      (firstSome [EoCases.__smtx_type_wf.case_0 x_a0, EoCases.__smtx_type_wf.case_1 x_a0, EoCases.__smtx_type_wf.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf
  unfold EoCases.__smtx_type_wf.case_0 EoCases.__smtx_type_wf.case_1 EoCases.__smtx_type_wf.case_2
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftype_5fwf_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24smtx_5ftype_5fwf_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  case_step with case_2_eo__24smtx_5ftype_5fwf_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_type_wf.case_0 EoCases.__smtx_type_wf.case_1 EoCases.__smtx_type_wf.case_2 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1001#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5ftype_5fwf s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_1001 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1001 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftype_5fwf_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf_5fcomponent s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_component.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_component.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf_5fcomponent
  have hG := Store.Grows.refl s
  store_step with ih.eo__24smtx_5finhabited_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 a0 _ hinv1 h64 (hG.rem hrem) h_a0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_and s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__smtx_type_wf_component.case_0 using

/-- logos's `__smtx_type_wf_component` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf_5fcomponent.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf_component x_a0 =
      (firstSome [EoCases.__smtx_type_wf_component.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf_component
  unfold EoCases.__smtx_type_wf_component.case_0
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf_5fcomponent s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_component x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf_5fcomponent.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf_5fcomponent
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftype_5fwf_5fcomponent_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_type_wf_component.case_0 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_5fcomponent_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf_5fcomponent.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf_5fcomponent
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftype_5fwf_5fcomponent s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf_component x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_5fcomponent_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf_rec.case_0
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf_rec.case_0 using

theorem case_1_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_type_wf_rec.case_1
  store_step with Store.native_bool_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_type_wf_rec.case_1 using

theorem case_2_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eMap.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_2
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24smtx_5finhabited_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_and s6 e_v9 (by rw [he_v9]; rfl) h_v5 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv7 hG with h_v9 in EoCases.__smtx_type_wf_rec.case_2 using

theorem case_3_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_3
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_type_wf_rec.case_3 using

theorem case_4_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_4
  store_step with ih.eo__24smtx_5finhabited_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s1 v1 _ hinv1 h64 (hG.rem hrem) h_v1 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_and s2 e_v4 (by rw [he_v4]; rfl) h_v2 h_v3 hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_type_wf_rec.case_4 using

theorem case_5_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_5
  store_step with ih.eo__24smtx_5fdd_5fhas_5fdt s v1 v2 _ _ hinv h64 hrem h_v1 h_v2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24smtx_5fdecl_5fwf_5frec s1 v2 v2 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_and s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__smtx_type_wf_rec.case_5 using

theorem case_6_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_6
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_type_wf_rec.case_6 using

theorem case_7_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_7
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_type_wf_rec.case_7 using

theorem case_8_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_type_wf_rec.case_8
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv1 hG with h_v3 in EoCases.__smtx_type_wf_rec.case_8 using

theorem case_9_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_type_wf_rec.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_type_wf_rec.case_9 using

theorem cases_0_0_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_0 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_1 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_2 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_0 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_1 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_2 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24smtx_5ftype_5fwf_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_4 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_5 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_6 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_5 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_6 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24smtx_5ftype_5fwf_5frec_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] = [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_type_wf_rec.case_8 x_a0 = none ∧ EoCases.__smtx_type_wf_rec.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_8 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_none hinv2 hG with ⟨hl_8, hl_9⟩

/-- logos's `__smtx_type_wf_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftype_5fwf_5frec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_type_wf_rec x_a0 =
      (firstSome [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __smtx_type_wf_rec
  unfold EoCases.__smtx_type_wf_rec.case_0 EoCases.__smtx_type_wf_rec.case_1 EoCases.__smtx_type_wf_rec.case_2 EoCases.__smtx_type_wf_rec.case_3 EoCases.__smtx_type_wf_rec.case_4 EoCases.__smtx_type_wf_rec.case_5 EoCases.__smtx_type_wf_rec.case_6 EoCases.__smtx_type_wf_rec.case_7 EoCases.__smtx_type_wf_rec.case_8 EoCases.__smtx_type_wf_rec.case_9
  logos_eq

theorem body_eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftype_5fwf_5frec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_type_wf_rec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftype_5fwf_5frec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftype_5fwf_5frec
  have hG := Store.Grows.refl s
  body_group_step with cases_0_0_eo__24smtx_5ftype_5fwf_5frec_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [] ++ [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  body_group_step with cases_0_1_eo__24smtx_5ftype_5fwf_5frec_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24smtx_5ftype_5fwf_5frec_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0, EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] = [EoCases.__smtx_type_wf_rec.case_0 x_a0, EoCases.__smtx_type_wf_rec.case_1 x_a0, EoCases.__smtx_type_wf_rec.case_2 x_a0, EoCases.__smtx_type_wf_rec.case_3 x_a0, EoCases.__smtx_type_wf_rec.case_4 x_a0, EoCases.__smtx_type_wf_rec.case_5 x_a0, EoCases.__smtx_type_wf_rec.case_6 x_a0, EoCases.__smtx_type_wf_rec.case_7 x_a0] ++ [EoCases.__smtx_type_wf_rec.case_8 x_a0, EoCases.__smtx_type_wf_rec.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_8, hl_9⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 in EoCases.__smtx_type_wf_rec.case_0 EoCases.__smtx_type_wf_rec.case_1 EoCases.__smtx_type_wf_rec.case_2 EoCases.__smtx_type_wf_rec.case_3 EoCases.__smtx_type_wf_rec.case_4 EoCases.__smtx_type_wf_rec.case_5 EoCases.__smtx_type_wf_rec.case_6 EoCases.__smtx_type_wf_rec.case_7 EoCases.__smtx_type_wf_rec.case_8 EoCases.__smtx_type_wf_rec.case_9 splitting x_a0

theorem eo__24smtx_5ftype_5fwf_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftype_5fwf_5frec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftype_5fwf_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1003#u32 _ [a0] rfl
    (fun s1 => body_eo__24smtx_5ftype_5fwf_5frec s1 a0) (fun s' t => Represents.rep s' t (__smtx_type_wf_rec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_1003 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1003 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftype_5fwf_5frec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.native_spec_Teq s e_v0 (by rw [he_v0]; rfl) h_a0 h_a1 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  have h_ite_v3 := (show if_0_eo__24smtx_5ftypeof_5f_3d s1 v0 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5f_3d
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v0 with ⟨hx_1, hbv_1⟩ | ⟨hx_1, hbv_1⟩
    · ite_branch hbv_1
      step as ⟨e_v1, he_v1⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
      ite_done hinv2 hG with (native_ite_true_rep _ hx_1 h_v1)
    · ite_branch hbv_1
      step as ⟨e_v2, he_v2⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v2 (by rw [he_v2]; exact empty_args) hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0
      ite_done hinv2 hG with (native_ite_false_rep _ hx_1 h_v2))
  store_step with h_ite_v3 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with ih.eo__24smtx_5ftypeof_5fguard s2 a0 v3 _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3
  case_done hinv3 hG with h_v4 in EoCases.__smtx_typeof_eq.case_0 using

/-- logos's `__smtx_typeof_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5f_3d.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_eq x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_eq.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_eq
  unfold EoCases.__smtx_typeof_eq.case_0
  logos_eq

theorem body_eo__24smtx_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5f_3d.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5f_3d_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__smtx_typeof_eq.case_0 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5f_3d_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5f_3d.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5f_3d
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5f_3d s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5f_3d_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_apply.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_apply.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eFunType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_apply.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_Teq s e_v3 (by rw [he_v3]; rfl) h_v1 h_a1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  have h_ite_v5 := (show if_0_eo__24smtx_5ftypeof_5fapply s1 v3 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fapply
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
  store_step with ih.eo__24smtx_5ftypeof_5fguard s2 v1 v5 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__smtx_typeof_apply.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_apply.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_apply.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__smtx_typeof_apply.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_Teq s e_v3 (by rw [he_v3]; rfl) h_v1 h_a1 hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  have h_ite_v5 := (show if_1_eo__24smtx_5ftypeof_5fapply s1 v3 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fapply
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
  store_step with ih.eo__24smtx_5ftypeof_5fguard s2 v1 v5 _ _ hinv2 h64 (hG.rem hrem) h_v1 h_v5 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__smtx_typeof_apply.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_apply.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_apply.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_apply.case_2 using

/-- logos's `__smtx_typeof_apply` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fapply.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_apply x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_apply.case_0 x_a0 x_a1, EoCases.__smtx_typeof_apply.case_1 x_a0 x_a1, EoCases.__smtx_typeof_apply.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_apply
  unfold EoCases.__smtx_typeof_apply.case_0 EoCases.__smtx_typeof_apply.case_1 EoCases.__smtx_typeof_apply.case_2
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_apply x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fapply.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fapply_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fapply_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5ftypeof_5fapply_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_typeof_apply.case_0 EoCases.__smtx_typeof_apply.case_1 EoCases.__smtx_typeof_apply.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fapply_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fapply.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fapply
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fapply s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_apply x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fapply_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_arith_overload_op_1.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_typeof_arith_overload_op_1.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_1.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_1.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_arith_overload_op_1.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__smtx_typeof_arith_overload_op_1.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_1.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_1.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_arith_overload_op_1.case_2 using

/-- logos's `__smtx_typeof_arith_overload_op_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_typeof_arith_overload_op_1 x_a0 =
      (firstSome [EoCases.__smtx_typeof_arith_overload_op_1.case_0 x_a0, EoCases.__smtx_typeof_arith_overload_op_1.case_1 x_a0, EoCases.__smtx_typeof_arith_overload_op_1.case_2 x_a0] default) := by
  conv => lhs; unfold __smtx_typeof_arith_overload_op_1
  unfold EoCases.__smtx_typeof_arith_overload_op_1.case_0 EoCases.__smtx_typeof_arith_overload_op_1.case_1 EoCases.__smtx_typeof_arith_overload_op_1.case_2
  logos_eq

theorem body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_arith_overload_op_1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  case_step with case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_typeof_arith_overload_op_1.case_0 EoCases.__smtx_typeof_arith_overload_op_1.case_1 EoCases.__smtx_typeof_arith_overload_op_1.case_2 splitting x_a0

theorem eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1 s1 a0) (fun s' t => Represents.rep s' t (__smtx_typeof_arith_overload_op_1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_2.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_2.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_arith_overload_op_2.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__smtx_typeof_arith_overload_op_2.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__smtx_typeof_arith_overload_op_2.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_2.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_2.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_arith_overload_op_2.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__smtx_typeof_arith_overload_op_2.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__smtx_typeof_arith_overload_op_2.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_2.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_2.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_arith_overload_op_2.case_2 using

/-- logos's `__smtx_typeof_arith_overload_op_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_arith_overload_op_2 x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_arith_overload_op_2.case_0 x_a0 x_a1, EoCases.__smtx_typeof_arith_overload_op_2.case_1 x_a0 x_a1, EoCases.__smtx_typeof_arith_overload_op_2.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_arith_overload_op_2
  unfold EoCases.__smtx_typeof_arith_overload_op_2.case_0 EoCases.__smtx_typeof_arith_overload_op_2.case_1 EoCases.__smtx_typeof_arith_overload_op_2.case_2
  logos_eq

theorem body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_arith_overload_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_typeof_arith_overload_op_2.case_0 EoCases.__smtx_typeof_arith_overload_op_2.case_1 EoCases.__smtx_typeof_arith_overload_op_2.case_2 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2 s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_arith_overload_op_2 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0
  case_done hinv2 hG with h_a2 in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1
  case_done hinv2 hG with h_a2 in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1 using

theorem case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_arith_overload_op_2_ret.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_arith_overload_op_2_ret.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_2 using

/-- logos's `__smtx_typeof_arith_overload_op_2_ret` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_arith_overload_op_2_ret x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_arith_overload_op_2_ret.case_2 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_arith_overload_op_2_ret
  unfold EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0 EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1 EoCases.__smtx_typeof_arith_overload_op_2_ret.case_2
  logos_eq

theorem body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_arith_overload_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  case_step with case_2_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__smtx_typeof_arith_overload_op_2_ret.case_0 EoCases.__smtx_typeof_arith_overload_op_2_ret.case_1 EoCases.__smtx_typeof_arith_overload_op_2_ret.case_2 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_arith_overload_op_2_ret x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5farith_5foverload_5fop_5f2_5fret_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_bv_op_1.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__smtx_typeof_bv_op_1.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_1.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_1.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_bv_op_1.case_1 using

/-- logos's `__smtx_typeof_bv_op_1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fbv_5fop_5f1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __smtx_typeof_bv_op_1 x_a0 =
      (firstSome [EoCases.__smtx_typeof_bv_op_1.case_0 x_a0, EoCases.__smtx_typeof_bv_op_1.case_1 x_a0] default) := by
  conv => lhs; unfold __smtx_typeof_bv_op_1
  unfold EoCases.__smtx_typeof_bv_op_1.case_0 EoCases.__smtx_typeof_bv_op_1.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24smtx_5ftypeof_5fbv_5fop_5f1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fbv_5fop_5f1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24smtx_5ftypeof_5fbv_5fop_5f1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_bv_op_1.case_0 EoCases.__smtx_typeof_bv_op_1.case_1 splitting x_a0

theorem eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fbv_5fop_5f1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24smtx_5ftypeof_5fbv_5fop_5f1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fbv_5fop_5f1 s1 a0) (fun s' t => Represents.rep s' t (__smtx_typeof_bv_op_1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_1_ret.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_1_ret.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_bv_op_1_ret.case_0
  case_done hinv hG with h_a1 in EoCases.__smtx_typeof_bv_op_1_ret.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_1_ret.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_1_ret.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_bv_op_1_ret.case_1 using

/-- logos's `__smtx_typeof_bv_op_1_ret` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_bv_op_1_ret x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_bv_op_1_ret.case_0 x_a0 x_a1, EoCases.__smtx_typeof_bv_op_1_ret.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_bv_op_1_ret
  unfold EoCases.__smtx_typeof_bv_op_1_ret.case_0 EoCases.__smtx_typeof_bv_op_1_ret.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_1_ret x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_bv_op_1_ret.case_0 EoCases.__smtx_typeof_bv_op_1_ret.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_bv_op_1_ret x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fbv_5fop_5f1_5fret_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
