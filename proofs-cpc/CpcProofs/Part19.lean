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

theorem case_0_eo__24tuple_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24tuple_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24tuple_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__tuple_collapse_updater_rhs.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__tuple_collapse_updater_rhs.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__tuple_collapse_updater_rhs.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same a2 v7 with h_a2 h_v7 using hinv2 else hinv2 hG in EoCases.__tuple_collapse_updater_rhs.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_tuple.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a1 _ _ hinv3 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__tuple_collapse_updater_rhs.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24tuple_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24tuple_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24tuple_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__tuple_collapse_updater_rhs.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__tuple_collapse_updater_rhs.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__tuple_collapse_updater_rhs.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s3 1#u32 (-1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_add s4 e_v10 (by rw [he_v10]; rfl) h_a2 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24tuple_5fcollapse_5fupdater_5frhs s5 v2 a1 v10 _ _ _ hinv5 h64 (hG.rem hrem) h_v2 h_a1 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__tuple_collapse_updater_rhs.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24tuple_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24tuple_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_collapse_updater_rhs.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_collapse_updater_rhs.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24tuple_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__tuple_collapse_updater_rhs.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__tuple_collapse_updater_rhs.case_2 using hn_a0 hn_a1 hn_a2

/-- logos's `__tuple_collapse_updater_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24tuple_5fcollapse_5fupdater_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __tuple_collapse_updater_rhs x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__tuple_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2, EoCases.__tuple_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2, EoCases.__tuple_collapse_updater_rhs.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __tuple_collapse_updater_rhs
  unfold EoCases.__tuple_collapse_updater_rhs.case_0 EoCases.__tuple_collapse_updater_rhs.case_1 EoCases.__tuple_collapse_updater_rhs.case_2
  logos_eq

theorem body_eo__24tuple_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24tuple_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__tuple_collapse_updater_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24tuple_5fcollapse_5fupdater_5frhs.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24tuple_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24tuple_5fcollapse_5fupdater_5frhs_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24tuple_5fcollapse_5fupdater_5frhs_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24tuple_5fcollapse_5fupdater_5frhs_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 in EoCases.__tuple_collapse_updater_rhs.case_0 EoCases.__tuple_collapse_updater_rhs.case_1 EoCases.__tuple_collapse_updater_rhs.case_2

theorem eo__24tuple_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24tuple_5fcollapse_5fupdater_5frhs.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24tuple_5fcollapse_5fupdater_5frhs
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1099#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24tuple_5fcollapse_5fupdater_5frhs s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__tuple_collapse_updater_rhs x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_1099 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1099 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24tuple_5fcollapse_5fupdater_5frhs_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24tuple_5fget_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24tuple_5fget_5fselectors_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_get_selectors_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_get_selectors_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24tuple_5fget_5fselectors_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__tuple_get_selectors_rec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__tuple_get_selectors_rec.case_0 using hn_a0 hn_a1

theorem case_1_eo__24tuple_5fget_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24tuple_5fget_5fselectors_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__tuple_get_selectors_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__tuple_get_selectors_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24tuple_5fget_5fselectors_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__tuple_get_selectors_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__tuple_get_selectors_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__tuple_get_selectors_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_tuple_2eselect.construct s2 e_v8 (by rw [he_v8]; rfl) h_a1 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with Store.builtin_spec_add s5 e_v11 (by rw [he_v11]; rfl) h_a1 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24tuple_5fget_5fselectors_5frec s6 v2 v11 _ _ hinv6 h64 (hG.rem hrem) h_v2 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_mk_rep s7 v9 v12 _ _ hinv7 h64 h_v9 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v13 in EoCases.__tuple_get_selectors_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__tuple_get_selectors_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24tuple_5fget_5fselectors_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __tuple_get_selectors_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__tuple_get_selectors_rec.case_0 x_a0 x_a1, EoCases.__tuple_get_selectors_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __tuple_get_selectors_rec
  unfold EoCases.__tuple_get_selectors_rec.case_0 EoCases.__tuple_get_selectors_rec.case_1
  logos_eq

theorem body_eo__24tuple_5fget_5fselectors_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24tuple_5fget_5fselectors_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__tuple_get_selectors_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24tuple_5fget_5fselectors_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24tuple_5fget_5fselectors_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24tuple_5fget_5fselectors_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24tuple_5fget_5fselectors_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__tuple_get_selectors_rec.case_0 EoCases.__tuple_get_selectors_rec.case_1

theorem eo__24tuple_5fget_5fselectors_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24tuple_5fget_5fselectors_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24tuple_5fget_5fselectors_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1100#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24tuple_5fget_5fselectors_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__tuple_get_selectors_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_1100 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1100 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24tuple_5fget_5fselectors_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
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
