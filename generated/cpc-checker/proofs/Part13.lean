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

theorem case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_decl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_decl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedd_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt_datatype_decl.case_0
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype s v2 _ hinv h64 hrem h_v2 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v3 _ hinv1 h64 (hG.rem hrem) h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fdd_2econs.construct s2 e_v6 (by rw [he_v6]; rfl) h_v1 h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv3 hG with h_v6 in EoCases.__eo_to_smt_datatype_decl.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_datatype_decl.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_datatype_decl.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_datatype_decl.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_datatype_decl.case_1 using

/-- logos's `__eo_to_smt_datatype_decl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_datatype_decl x_a0 =
      (firstSome [EoCases.__eo_to_smt_datatype_decl.case_0 x_a0, EoCases.__eo_to_smt_datatype_decl.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_datatype_decl
  unfold EoCases.__eo_to_smt_datatype_decl.case_0 EoCases.__eo_to_smt_datatype_decl.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_datatype_decl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_datatype_decl.case_0 EoCases.__eo_to_smt_datatype_decl.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fdatatype_5fdecl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fdatatype_5fdecl
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 751#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_datatype_decl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_751 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_751 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fexists_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fto_5fsmt_5fexists s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_exists.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_exists.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fexists
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_exists.case_0
  case_done hinv1 hG with h_a1 in EoCases.__eo_to_smt_exists.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fexists_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fto_5fsmt_5fexists s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_exists.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_exists.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fexists
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_exists.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_exists.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_exists.case_1
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__eo_to_smt_exists.case_1
  pat_destruct_lit Store.destruct_string_spec s1 v8 h_v8 hinv1 h64 as ⟨v11, x_v11, h_v11⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 in EoCases.__eo_to_smt_exists.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v9 _ hinv2 h64 (hG.rem hrem) h_v9 as ⟨v12, s3, hinv3, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11
  store_step with ih.eo__24eo_5fto_5fsmt_5fexists s3 v2 a1 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eexists.construct s4 e_v14 (by rw [he_v14]; rfl) h_v11 h_v12 h_v13 hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  case_done hinv5 hG with h_v14 in EoCases.__eo_to_smt_exists.case_1 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24eo_5fto_5fsmt_5fexists_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24eo_5fto_5fsmt_5fexists s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_exists.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_exists.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5fexists
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_exists.case_2 using

/-- logos's `__eo_to_smt_exists` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fexists.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_to_smt_exists x_a0 x_a1 =
      (firstSome [EoCases.__eo_to_smt_exists.case_0 x_a0 x_a1, EoCases.__eo_to_smt_exists.case_1 x_a0 x_a1, EoCases.__eo_to_smt_exists.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_to_smt_exists
  unfold EoCases.__eo_to_smt_exists.case_0 EoCases.__eo_to_smt_exists.case_1 EoCases.__eo_to_smt_exists.case_2
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fexists_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fto_5fsmt_5fexists s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_exists x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fexists.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fto_5fsmt_5fexists
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fexists_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fexists_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24eo_5fto_5fsmt_5fexists_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_to_smt_exists.case_0 EoCases.__eo_to_smt_exists.case_1 EoCases.__eo_to_smt_exists.case_2 splitting x_a0 x_a1

theorem eo__24eo_5fto_5fsmt_5fexists_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fexists.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fto_5fsmt_5fexists
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 754#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fexists s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_to_smt_exists x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_754 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_754 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fexists_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_lambda_curry.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_lambda_curry.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_lambda_curry.case_0
  case_done hinv1 hG with h_a1 in EoCases.__eo_to_smt_lambda_curry.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fto_5fsmt_5flambda_5fcurry s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_lambda_curry.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_lambda_curry.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5flambda_5fcurry
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_lambda_curry.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_lambda_curry.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_lambda_curry.case_1
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__eo_to_smt_lambda_curry.case_1
  pat_destruct_lit Store.destruct_string_spec s1 v8 h_v8 hinv1 h64 as ⟨v11, x_v11, h_v11⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 in EoCases.__eo_to_smt_lambda_curry.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v9 _ hinv2 h64 (hG.rem hrem) h_v9 as ⟨v12, s3, hinv3, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11
  store_step with ih.eo__24smtx_5ftype_5fwf_5fcomponent s3 v12 _ hinv3 h64 (hG.rem hrem) h_v12 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  have h_ite_v18 := (show if_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry s4 v13 v9 v2 a1 v11 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v13 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
    · ite_branch hbv_14
      store_step with ih.eo__24eo_5fto_5fsmt_5ftype s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
      store_step with ih.eo__24eo_5fto_5fsmt_5flambda_5fcurry s5 v2 a1 _ _ hinv5 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v15, s6, hinv6, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
      step as ⟨e_v16, he_v16⟩
      store_step with CtorSpec.eo__24emb_5fsm_2elam.construct s6 e_v16 (by rw [he_v16]; rfl) h_v11 h_v14 h_v15 hinv6 h64 as ⟨v16, s7, hinv7, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
      ite_done hinv7 hG with (native_ite_true_rep _ hx_14 h_v16)
    · ite_branch hbv_14
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s4 e_v17 (by rw [he_v17]; exact empty_args) hinv4 h64 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
      ite_done hinv5 hG with (native_ite_false_rep _ hx_14 h_v17))
  store_step with h_ite_v18 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  case_done hinv5 hG with h_v18 in EoCases.__eo_to_smt_lambda_curry.case_1 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24eo_5fto_5fsmt_5flambda_5fcurry s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_lambda_curry.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_lambda_curry.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5flambda_5fcurry
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_lambda_curry.case_2 using

/-- logos's `__eo_to_smt_lambda_curry` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5flambda_5fcurry.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_to_smt_lambda_curry x_a0 x_a1 =
      (firstSome [EoCases.__eo_to_smt_lambda_curry.case_0 x_a0 x_a1, EoCases.__eo_to_smt_lambda_curry.case_1 x_a0 x_a1, EoCases.__eo_to_smt_lambda_curry.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_to_smt_lambda_curry
  unfold EoCases.__eo_to_smt_lambda_curry.case_0 EoCases.__eo_to_smt_lambda_curry.case_1 EoCases.__eo_to_smt_lambda_curry.case_2
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fto_5fsmt_5flambda_5fcurry s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_lambda_curry x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5flambda_5fcurry.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fto_5fsmt_5flambda_5fcurry
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_to_smt_lambda_curry.case_0 EoCases.__eo_to_smt_lambda_curry.case_1 EoCases.__eo_to_smt_lambda_curry.case_2 splitting x_a0 x_a1

theorem eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5flambda_5fcurry.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fto_5fsmt_5flambda_5fcurry
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 755#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5flambda_5fcurry s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_to_smt_lambda_curry x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_755 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_755 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5flambda_5fcurry_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fnat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fnat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_nat.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_nat.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fnat
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_numeral_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt_nat.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.native_spec_int_to_nat s1 e_v2 (by rw [he_v2]; rfl) h_v1 hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  rw [← Bridge.native_int_to_nat] at h_v2
  case_done hinv2 hG with h_v2 in EoCases.__eo_to_smt_nat.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fnat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fnat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_nat.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_nat.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fnat
  have hG := Store.Grows.refl s
  store_step with Store.native_nat_zero_spec s hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_nat.case_1 using

/-- logos's `__eo_to_smt_nat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fnat.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_nat x_a0 =
      (firstSome [EoCases.__eo_to_smt_nat.case_0 x_a0, EoCases.__eo_to_smt_nat.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_nat
  unfold EoCases.__eo_to_smt_nat.case_0 EoCases.__eo_to_smt_nat.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fnat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fnat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_nat x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fnat.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fnat
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fnat_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fnat_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_nat.case_0 EoCases.__eo_to_smt_nat.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fnat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fnat.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fnat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fnat s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_nat x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fnat_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_nat_is_valid.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_nat_is_valid.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.destruct_numeral_spec s a0 h_a0 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 in EoCases.__eo_to_smt_nat_is_valid.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with Store.native_spec_zleq s2 e_v3 (by rw [he_v3]; rfl) h_v2 h_v1 hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  rw [← Bridge.native_zleq] at h_v3
  case_done hinv3 hG with h_v3 in EoCases.__eo_to_smt_nat_is_valid.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_nat_is_valid.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_nat_is_valid.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_nat_is_valid.case_1 using

/-- logos's `__eo_to_smt_nat_is_valid` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_nat_is_valid x_a0 =
      (firstSome [EoCases.__eo_to_smt_nat_is_valid.case_0 x_a0, EoCases.__eo_to_smt_nat_is_valid.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_to_smt_nat_is_valid
  unfold EoCases.__eo_to_smt_nat_is_valid.case_0 EoCases.__eo_to_smt_nat_is_valid.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_nat_is_valid x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_nat_is_valid.case_0 EoCases.__eo_to_smt_nat_is_valid.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_nat_is_valid x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fnat_5fis_5fvalid_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_to_smt_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_to_smt_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2 = some (__eo_to_smt_quantifiers_skolemize y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_to_smt_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_0
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_0
  pat_destruct_lit Store.destruct_string_spec s1 v8 h_v8 hinv1 h64 as ⟨v11, x_v11, h_v11⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 in EoCases.__eo_to_smt_quantifiers_skolemize.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s2 a2 h_a2 hinv2 h64 storing ⟨s3, hinv3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 in EoCases.__eo_to_smt_quantifiers_skolemize.case_0
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11
  store_step with ih.eo__24eo_5fto_5fsmt_5fexists s4 v2 a1 _ _ hinv4 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24emb_5fsm_2echoice.construct s5 e_v15 (by rw [he_v15]; rfl) h_v11 h_v13 h_v14 hinv5 h64 as ⟨v15, s6, hinv6, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14
  case_done hinv6 hG with h_v15 in EoCases.__eo_to_smt_quantifiers_skolemize.case_0 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_to_smt_quantifiers_skolemize.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_to_smt_quantifiers_skolemize.case_1 x_a0 x_a1 x_a2 = some (__eo_to_smt_quantifiers_skolemize y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_to_smt_quantifiers_skolemize.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize more_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_1
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__eo_to_smt_quantifiers_skolemize.case_1
  pat_destruct_lit Store.destruct_string_spec s1 v8 h_v8 hinv1 h64 as ⟨v11, x_v11, h_v11⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 in EoCases.__eo_to_smt_quantifiers_skolemize.case_1
  pat_destruct_lit Store.native_pattern_succ_spec s2 a2 h_a2 hinv2 h64 as ⟨v13, x_v13, h_v13⟩ storing ⟨s3, hinv3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 in EoCases.__eo_to_smt_quantifiers_skolemize.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14
  store_step with ih.eo__24eo_5fto_5fsmt_5fexists s5 v2 a1 _ _ hinv5 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24emb_5fsm_2echoice.construct s6 e_v17 (by rw [he_v17]; rfl) h_v11 h_v15 h_v16 hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__24emb_5fsbd_2enil.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24emb_5fsbd_2econs.construct s8 e_v19 (by rw [he_v19]; rfl) h_v11 h_v14 h_v17 h_v18 hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24emb_5fsm_2ebind.construct s9 e_v20 (by rw [he_v20]; rfl) h_v19 h_a1 hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  case_again hinv10 hG with h_v2 h_v20 h_v13 in EoCases.__eo_to_smt_quantifiers_skolemize.case_1 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_to_smt_quantifiers_skolemize.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_to_smt_quantifiers_skolemize.case_2 x_a0 x_a1 x_a2 = some (__eo_to_smt_quantifiers_skolemize y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_to_smt_quantifiers_skolemize.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_quantifiers_skolemize.case_2 using

/-- logos's `__eo_to_smt_quantifiers_skolemize` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_to_smt_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2, EoCases.__eo_to_smt_quantifiers_skolemize.case_1 x_a0 x_a1 x_a2, EoCases.__eo_to_smt_quantifiers_skolemize.case_2 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_to_smt_quantifiers_skolemize
  unfold EoCases.__eo_to_smt_quantifiers_skolemize.case_0 EoCases.__eo_to_smt_quantifiers_skolemize.case_1 EoCases.__eo_to_smt_quantifiers_skolemize.case_2
  logos_eq

theorem step_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2 = __eo_to_smt_quantifiers_skolemize y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_stuck hinv4 hG using hc0 hc1 hc2 in EoCases.__eo_to_smt_quantifiers_skolemize.case_0 EoCases.__eo_to_smt_quantifiers_skolemize.case_1 EoCases.__eo_to_smt_quantifiers_skolemize.case_2 splitting x_a0 x_a1 x_a2

theorem body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_loop
  step with step_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 758#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_to_smt_quantifiers_skolemize x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_758 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_758 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fquantifiers_5fskolemize_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_to_smt_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_to_smt_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2 = some (__eo_to_smt_re_unfold_pos_component y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_to_smt_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2e_2b_2b.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_re_unfold_pos_component.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s a2 h_a2 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__eo_to_smt_re_unfold_pos_component.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNumeral.construct s2 e_v5 (by rw [he_v5]; rfl) h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit.construct s3 e_v6 (by rw [he_v6]; rfl) h_a0 h_v1 h_v2 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s4 e_v7 (by rw [he_v7]; rfl) h_a0 h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v7 in EoCases.__eo_to_smt_re_unfold_pos_component.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_to_smt_re_unfold_pos_component.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_to_smt_re_unfold_pos_component.case_1 x_a0 x_a1 x_a2 = some (__eo_to_smt_re_unfold_pos_component y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_to_smt_re_unfold_pos_component.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2ere_2e_2b_2b.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_re_unfold_pos_component.case_1
  pat_destruct_lit Store.native_pattern_succ_spec s a2 h_a2 hinv h64 as ⟨v4, x_v4, h_v4⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 in EoCases.__eo_to_smt_re_unfold_pos_component.case_1
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit.construct s1 e_v5 (by rw [he_v5]; rfl) h_a0 h_v1 h_v2 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2elen.construct s2 e_v6 (by rw [he_v6]; rfl) h_a0 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit.construct s3 e_v7 (by rw [he_v7]; rfl) h_a0 h_v1 h_v2 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fsm_2e_2d.construct s4 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct s5 e_v9 (by rw [he_v9]; rfl) h_a0 h_v5 h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  case_again hinv6 hG with h_v9 h_v2 h_v4 in EoCases.__eo_to_smt_re_unfold_pos_component.case_1 using

theorem case_2_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_2_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_to_smt_re_unfold_pos_component.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__eo_to_smt_re_unfold_pos_component.case_2 x_a0 x_a1 x_a2 = some (__eo_to_smt_re_unfold_pos_component y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__eo_to_smt_re_unfold_pos_component.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_re_unfold_pos_component.case_2 using

/-- logos's `__eo_to_smt_re_unfold_pos_component` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_to_smt_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2, EoCases.__eo_to_smt_re_unfold_pos_component.case_1 x_a0 x_a1 x_a2, EoCases.__eo_to_smt_re_unfold_pos_component.case_2 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_to_smt_re_unfold_pos_component
  unfold EoCases.__eo_to_smt_re_unfold_pos_component.case_0 EoCases.__eo_to_smt_re_unfold_pos_component.case_1 EoCases.__eo_to_smt_re_unfold_pos_component.case_2
  logos_eq

theorem step_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2 = __eo_to_smt_re_unfold_pos_component y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  round_step with case_0_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using
  round_step with case_1_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0
  round_step with case_2_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hc0 hc1
  round_stuck hinv4 hG using hc0 hc1 hc2 in EoCases.__eo_to_smt_re_unfold_pos_component.case_0 EoCases.__eo_to_smt_re_unfold_pos_component.case_1 EoCases.__eo_to_smt_re_unfold_pos_component.case_2 splitting x_a0 x_a1 x_a2

theorem body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_loop
  step with step_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 759#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_to_smt_re_unfold_pos_component x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_759 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_759 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fre_5funfold_5fpos_5fcomponent_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_reserved_datatype_name.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_reserved_datatype_name.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s _ _ rfl hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  replace h_v0 := Represents.rep_of_eq h_v0 (y := SmtEval.native_string_lit "@") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v0]; decide)
  step as ⟨e_v1, he_v1⟩
  store_step with Store.native_spec_string_prefix_eq s1 e_v1 (by rw [he_v1]; rfl) h_v0 h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  rw [← Bridge.native_string_prefix_eq] at h_v1
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_reserved_datatype_name.case_0 using

/-- logos's `__eo_to_smt_reserved_datatype_name` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_reserved_datatype_name x_a0 =
      (firstSome [EoCases.__eo_to_smt_reserved_datatype_name.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_to_smt_reserved_datatype_name
  unfold EoCases.__eo_to_smt_reserved_datatype_name.case_0
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_reserved_datatype_name x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_to_smt_reserved_datatype_name.case_0 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_reserved_datatype_name x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_seq_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_seq_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fseq_2eempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSeq.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_seq_empty.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eseq_2eempty.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_to_smt_seq_empty.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_seq_empty.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_seq_empty.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fseq_2eempty
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_seq_empty.case_1 using

/-- logos's `__eo_to_smt_seq_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fseq_2eempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_seq_empty x_a0 =
      (firstSome [EoCases.__eo_to_smt_seq_empty.case_0 x_a0, EoCases.__eo_to_smt_seq_empty.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_seq_empty
  unfold EoCases.__eo_to_smt_seq_empty.case_0 EoCases.__eo_to_smt_seq_empty.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_seq_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fseq_2eempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fseq_2eempty
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fseq_2eempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fseq_2eempty_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_seq_empty.case_0 EoCases.__eo_to_smt_seq_empty.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fseq_2eempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fseq_2eempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fseq_2eempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fseq_2eempty s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_seq_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fseq_2eempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_set_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_set_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fset_2eempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_set_empty.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eset_2eempty.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_to_smt_set_empty.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_set_empty.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_set_empty.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fset_2eempty
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_set_empty.case_1 using

/-- logos's `__eo_to_smt_set_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fset_2eempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_set_empty x_a0 =
      (firstSome [EoCases.__eo_to_smt_set_empty.case_0 x_a0, EoCases.__eo_to_smt_set_empty.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_set_empty
  unfold EoCases.__eo_to_smt_set_empty.case_0 EoCases.__eo_to_smt_set_empty.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_set_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fset_2eempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fset_2eempty
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fset_2eempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fset_2eempty_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_set_empty.case_0 EoCases.__eo_to_smt_set_empty.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fset_2eempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fset_2eempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fset_2eempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fset_2eempty s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_set_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fset_2eempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_set_elem_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_set_elem_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_set_elem_type.case_0
  case_done hinv hG with h_v1 in EoCases.__eo_to_smt_set_elem_type.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_set_elem_type.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_set_elem_type.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_set_elem_type.case_1 using

/-- logos's `__eo_to_smt_set_elem_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fset_5felem_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_set_elem_type x_a0 =
      (firstSome [EoCases.__eo_to_smt_set_elem_type.case_0 x_a0, EoCases.__eo_to_smt_set_elem_type.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_set_elem_type
  unfold EoCases.__eo_to_smt_set_elem_type.case_0 EoCases.__eo_to_smt_set_elem_type.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_set_elem_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fset_5felem_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_set_elem_type.case_0 EoCases.__eo_to_smt_set_elem_type.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fset_5felem_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5fset_5felem_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_set_elem_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fset_5felem_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_0_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_sets_deq_diff.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_sets_deq_diff.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_sets_deq_diff.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eSet.destruct h_a3 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt_sets_deq_diff.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fsm_2emap_5fdiff.construct s e_v4 (by rw [he_v4]; rfl) h_a0 h_a2 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3
  case_done hinv1 hG with h_v4 in EoCases.__eo_to_smt_sets_deq_diff.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    case_1_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_sets_deq_diff.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_sets_deq_diff.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_sets_deq_diff.case_1 using

/-- logos's `__eo_to_smt_sets_deq_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_to_smt_sets_deq_diff x_a0 x_a1 x_a2 x_a3 =
      (firstSome [EoCases.__eo_to_smt_sets_deq_diff.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__eo_to_smt_sets_deq_diff.case_1 x_a0 x_a1 x_a2 x_a3] default) := by
  conv => lhs; unfold __eo_to_smt_sets_deq_diff
  unfold EoCases.__eo_to_smt_sets_deq_diff.case_0 EoCases.__eo_to_smt_sets_deq_diff.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_sets_deq_diff x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_sets_deq_diff.case_0 EoCases.__eo_to_smt_sets_deq_diff.case_1 splitting x_a0 x_a1 x_a2 x_a3

theorem eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_to_smt_sets_deq_diff x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fsets_5fdeq_5fdiff_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftester_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5ftester s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tester.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tester.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftester
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtCons.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_to_smt_tester.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eDtTester.construct s e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv1 hG with h_v4 in EoCases.__eo_to_smt_tester.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5ftester_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5ftester s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tester.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tester.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5ftester
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_tester.case_1 using

/-- logos's `__eo_to_smt_tester` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftester.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_tester x_a0 =
      (firstSome [EoCases.__eo_to_smt_tester.case_0 x_a0, EoCases.__eo_to_smt_tester.case_1 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_tester
  unfold EoCases.__eo_to_smt_tester.case_0 EoCases.__eo_to_smt_tester.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftester_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5ftester s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tester x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftester.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5ftester
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5ftester_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5ftester_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_tester.case_0 EoCases.__eo_to_smt_tester.case_1 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5ftester_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftester.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5ftester
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftester s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_tester x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftester_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftuple_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5ftuple_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tuple_decl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tuple_decl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftuple_5fdecl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s _ _ rfl hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  replace h_v0 := Represents.rep_of_eq h_v0 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v0]; decide)
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fdd_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_a0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_to_smt_tuple_decl.case_0 using

/-- logos's `__eo_to_smt_tuple_decl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftuple_5fdecl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_tuple_decl x_a0 =
      (firstSome [EoCases.__eo_to_smt_tuple_decl.case_0 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_tuple_decl
  unfold EoCases.__eo_to_smt_tuple_decl.case_0
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tuple_decl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftuple_5fdecl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5ftuple_5fdecl_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_to_smt_tuple_decl.case_0 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5ftuple_5fdecl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftuple_5fdecl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5ftuple_5fdecl
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_tuple_decl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftuple_5fdecl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tuple_prepend_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tuple_prepend_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec
  have hG := Store.Grows.refl s
  pat_native_zero Store.native_pattern_nat_zero_spec s a3 h_a3 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 in EoCases.__eo_to_smt_tuple_prepend_rec.case_0
  case_done hinv1 hG with h_a4 in EoCases.__eo_to_smt_tuple_prepend_rec.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tuple_prepend_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tuple_prepend_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec
  have hG := Store.Grows.refl s
  pat_destruct_lit Store.native_pattern_succ_spec s a3 h_a3 hinv h64 as ⟨v1, x_v1, h_v1⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 in EoCases.__eo_to_smt_tuple_prepend_rec.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec s1 a0 a1 a2 v1 a4 _ _ _ _ _ hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_v1 h_a4 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1
  step as ⟨e_v3, he_v3⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2
  replace h_v3 := Represents.rep_of_eq h_v3 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v3]; decide)
  store_step with Store.native_nat_zero_spec s3 hinv3 h64 as ⟨v4, s4, hinv4, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eDtSel.construct s4 e_v5 (by rw [he_v5]; rfl) h_v3 h_a0 h_v4 h_v1 hinv4 h64 as ⟨v5, s5, hinv5, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s5 e_v6 (by rw [he_v6]; rfl) h_v5 h_a2 hinv5 h64 as ⟨v6, s6, hinv6, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s6 e_v7 (by rw [he_v7]; rfl) h_v2 h_v6 hinv6 h64 as ⟨v7, s7, hinv7, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv7 hG with h_v7 in EoCases.__eo_to_smt_tuple_prepend_rec.case_1 using

/-- logos's `__eo_to_smt_tuple_prepend_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_to_smt_tuple_prepend_rec x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_to_smt_tuple_prepend_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_to_smt_tuple_prepend_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4] default) := by
  conv => lhs; unfold __eo_to_smt_tuple_prepend_rec
  unfold EoCases.__eo_to_smt_tuple_prepend_rec.case_0 EoCases.__eo_to_smt_tuple_prepend_rec.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tuple_prepend_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_tuple_prepend_rec.case_0 EoCases.__eo_to_smt_tuple_prepend_rec.case_1 splitting x_a0 x_a1 x_a2 x_a3 x_a4

theorem eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 769#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_to_smt_tuple_prepend_rec x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_769 hsem
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
      exact ProgramSem.to_769 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftuple_5fprepend_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tuple_select.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tuple_select.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect more_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_tuple_select.case_0
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_v2 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ ⟨v6, x_v6, h_v6⟩ else hinv hG in EoCases.__eo_to_smt_tuple_select.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s e_v7 (by rw [he_v7]; exact empty_args) hinv h64 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same v6 v7 with h_v6 h_v7 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_tuple_select.case_0
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a1 as ⟨v9, x_v9, h_v9⟩ else hinv1 hG in EoCases.__eo_to_smt_tuple_select.case_0
  step as ⟨e_v10, he_v10⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s1 _ _ rfl hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9
  replace h_v10 := Represents.rep_of_eq h_v10 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v10]; decide)
  step as ⟨e_v11, he_v11⟩
  store_step with Store.native_spec_streq s2 e_v11 (by rw [he_v11]; rfl) h_v1 h_v10 hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10
  rw [← Bridge.native_streq] at h_v11
  step as ⟨e_v12, he_v12⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11
  replace h_v12 := Represents.rep_of_eq h_v12 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v12]; decide)
  step as ⟨e_v13, he_v13⟩
  store_step with Store.native_spec_streq s4 e_v13 (by rw [he_v13]; rfl) h_v4 h_v12 hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12
  rw [← Bridge.native_streq] at h_v13
  step as ⟨e_v14, he_v14⟩
  store_step with Store.native_spec_and s5 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13
  rw [← Bridge.native_and] at h_v14
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.native_spec_zleq s7 e_v16 (by rw [he_v16]; rfl) h_v15 h_v9 hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  rw [← Bridge.native_zleq] at h_v16
  step as ⟨e_v17, he_v17⟩
  store_step with Store.native_spec_and s8 e_v17 (by rw [he_v17]; rfl) h_v14 h_v16 hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  rw [← Bridge.native_and] at h_v17
  have h_ite_v25 := (show if_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect s9 v17 v5 v9 a2 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    rcases Store.boolean_value_native h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
    · ite_branch hbv_18
      step as ⟨e_v18, he_v18⟩
      try simp only [eostring.EoString.from_code_points, Std.bind_ok]
      store_step with Store.raw_str_vec_spec s9 _ _ rfl hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      replace h_v18 := Represents.rep_of_eq h_v18 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v18]; decide)
      store_step with ih.eo__24eo_5fto_5fsmt_5ftuple_5fdecl s10 v5 _ hinv10 h64 (hG.rem hrem) h_v5 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      store_step with Store.native_nat_zero_spec s11 hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      step as ⟨e_v21, he_v21⟩
      store_step with Store.native_spec_int_to_nat s12 e_v21 (by rw [he_v21]; rfl) h_v9 hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      rw [← Bridge.native_int_to_nat] at h_v21
      step as ⟨e_v22, he_v22⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eDtSel.construct s13 e_v22 (by rw [he_v22]; rfl) h_v18 h_v19 h_v20 h_v21 hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s14 e_v23 (by rw [he_v23]; rfl) h_v22 h_a2 hinv14 h64 as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      ite_done hinv15 hG with (native_ite_true_rep _ hx_18 h_v23)
    · ite_branch hbv_18
      step as ⟨e_v24, he_v24⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s9 e_v24 (by rw [he_v24]; exact empty_args) hinv9 h64 as ⟨v24, s10, hinv10, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      ite_done hinv10 hG with (native_ite_false_rep _ hx_18 h_v24))
  store_step with h_ite_v25 as ⟨v25, s10, hinv10, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv10 hG with h_v25 in EoCases.__eo_to_smt_tuple_select.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_tuple_select.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_tuple_select.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_tuple_select.case_1 using

/-- logos's `__eo_to_smt_tuple_select` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftuple_5fselect.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_to_smt_tuple_select x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_to_smt_tuple_select.case_0 x_a0 x_a1 x_a2, EoCases.__eo_to_smt_tuple_select.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_to_smt_tuple_select
  unfold EoCases.__eo_to_smt_tuple_select.case_0 EoCases.__eo_to_smt_tuple_select.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fto_5fsmt_5ftuple_5fselect s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_tuple_select x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftuple_5fselect.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fto_5fsmt_5ftuple_5fselect
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_tuple_select.case_0 EoCases.__eo_to_smt_tuple_select.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftuple_5fselect.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fto_5fsmt_5ftuple_5fselect
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftuple_5fselect s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_to_smt_tuple_select x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftuple_5fselect_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_type.case_1
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  have h_ite_v7 := (show if_0_eo__24eo_5fto_5fsmt_5ftype s1 v3 v2 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (native_ite_true_rep _ hx_4 h_v4)
    · ite_branch hbv_4
      store_step with ih.eo__24eo_5fto_5fsmt_5fdatatype_5fdecl s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s2 e_v6 (by rw [he_v6]; rfl) h_v1 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5
      ite_done hinv3 hG with (native_ite_false_rep _ hx_4 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v7 in EoCases.__eo_to_smt_type.case_1 using

theorem case_2_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDatatypeTypeRef.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_type.case_2
  store_step with ih.eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  have h_ite_v5 := (show if_1_eo__24eo_5fto_5fsmt_5ftype s1 v2 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v2 with ⟨hx_3, hbv_3⟩ | ⟨hx_3, hbv_3⟩
    · ite_branch hbv_3
      step as ⟨e_v3, he_v3⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v3 (by rw [he_v3]; exact empty_args) hinv1 h64 as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_true_rep _ hx_3 h_v3)
    · ite_branch hbv_3
      step as ⟨e_v4, he_v4⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eTypeRef.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2
      ite_done hinv2 hG with (native_ite_false_rep _ hx_3 h_v4))
  store_step with h_ite_v5 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2
  case_done hinv2 hG with h_v5 in EoCases.__eo_to_smt_type.case_2 using

theorem case_3_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_3_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_type.case_3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v1 _ hinv h64 hrem h_v1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDtcAppType.construct s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24smtx_5ftypeof_5fguard s5 v4 v7 _ _ hinv5 h64 (hG.rem hrem) h_v4 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24smtx_5ftypeof_5fguard s6 v3 v8 _ _ hinv6 h64 (hG.rem hrem) h_v3 h_v8 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  case_done hinv7 hG with h_v9 in EoCases.__eo_to_smt_type.case_3 using

theorem case_4_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_4_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fUSort.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_to_smt_type.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eUSort.construct s e_v2 (by rw [he_v2]; rfl) h_v1 hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_to_smt_type.case_4 using

theorem case_5_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_5_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_5
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_5
  pat_is_node h_v4 : x_v4 is Eo.Term.FunType by Embed.inv_Term_FunType else hinv hG in EoCases.__eo_to_smt_type.case_5
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s v5 _ hinv h64 hrem h_v5 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v5 _ hinv2 h64 (hG.rem hrem) h_v5 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v10, s4, hinv4, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eFunType.construct s4 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv4 h64 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24smtx_5ftypeof_5fguard s5 v8 v11 _ _ hinv5 h64 (hG.rem hrem) h_v8 h_v11 as ⟨v12, s6, hinv6, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24smtx_5ftypeof_5fguard s6 v7 v12 _ _ hinv6 h64 (hG.rem hrem) h_v7 h_v12 as ⟨v13, s7, hinv7, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv7 hG with h_v13 in EoCases.__eo_to_smt_type.case_5 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_6_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_6_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_6
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eInt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_6 using

theorem case_7_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_7_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_7
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eReal.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_7 using

theorem case_8_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_8_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_8
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_8
  pat_destruct_lit Store.destruct_numeral_spec s1 v2 h_v2 hinv1 h64 as ⟨v5, x_v5, h_v5⟩ storing ⟨s2, hinv2⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 in EoCases.__eo_to_smt_type.case_8
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zleq s3 e_v7 (by rw [he_v7]; rfl) h_v6 h_v5 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6
  rw [← Bridge.native_zleq] at h_v7
  have h_ite_v11 := (show if_2_eo__24eo_5fto_5fsmt_5ftype s4 v7 v5 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_int_to_nat s4 e_v8 (by rw [he_v8]; rfl) h_v5 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7
      rw [← Bridge.native_int_to_nat] at h_v8
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s5 e_v9 (by rw [he_v9]; rfl) h_v8 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7 h_v8
      ite_done hinv6 hG with (native_ite_true_rep _ hx_8 h_v9)
    · ite_branch hbv_8
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7
      ite_done hinv5 hG with (native_ite_false_rep _ hx_8 h_v10))
  store_step with h_ite_v11 as ⟨v11, s5, hinv5, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v11 in EoCases.__eo_to_smt_type.case_8 using hn_v1 hn_v2

theorem case_9_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_9_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Char.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_9
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eChar.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_9 using

theorem case_10_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_10_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_10
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_10
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSeq.construct s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fguard s4 v4 v6 _ _ hinv4 h64 (hG.rem hrem) h_v4 h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v7 in EoCases.__eo_to_smt_type.case_10 using hn_v1 hn_v2

theorem case_11_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_11_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_11
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_11
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Array.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_11
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eMap.construct s5 e_v11 (by rw [he_v11]; rfl) h_v9 h_v10 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24smtx_5ftypeof_5fguard s6 v8 v11 _ _ hinv6 h64 (hG.rem hrem) h_v8 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24smtx_5ftypeof_5fguard s7 v7 v12 _ _ hinv7 h64 (hG.rem hrem) h_v7 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  case_done hinv8 hG with h_v13 in EoCases.__eo_to_smt_type.case_11 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_12_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_12_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_RegLan.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_12
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eRegLan.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_to_smt_type.case_12 using

theorem case_13_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_13_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_UnitTuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_13
  step as ⟨e_v1, he_v1⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s1 _ _ rfl hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  replace h_v1 := Represents.rep_of_eq h_v1 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v1]; decide)
  step as ⟨e_v2, he_v2⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  replace h_v2 := Represents.rep_of_eq h_v2 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v2]; decide)
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24emb_5fdtc_2eunit.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s5 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fdd_2econs.construct s7 e_v7 (by rw [he_v7]; rfl) h_v2 h_v5 h_v6 hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s8 e_v8 (by rw [he_v8]; rfl) h_v1 h_v7 hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_to_smt_type.case_13 using

theorem case_14_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_14_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_14
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_14
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_14
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype_5ftuple s3 v7 v8 _ _ hinv3 h64 (hG.rem hrem) h_v7 h_v8 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24smtx_5ftype_5fwf s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  have h_ite_v15 := (show if_3_eo__24eo_5fto_5fsmt_5ftype s5 v10 v5 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_3_eo__24eo_5fto_5fsmt_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    rcases Store.boolean_value_native h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      store_step with ih.eo__24eo_5fto_5fsmt_5ftype s5 v5 _ hinv5 h64 (hG.rem hrem) h_v5 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      store_step with ih.eo__24eo_5fto_5fsmt_5ftype s6 v2 _ hinv6 h64 (hG.rem hrem) h_v2 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
      store_step with ih.eo__24eo_5fto_5fsmt_5ftype_5ftuple s7 v11 v12 _ _ hinv7 h64 (hG.rem hrem) h_v11 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
      ite_done hinv8 hG with (native_ite_true_rep _ hx_11 h_v13)
    · ite_branch hbv_11
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv6 hG with (native_ite_false_rep _ hx_11 h_v14))
  store_step with h_ite_v15 as ⟨v15, s6, hinv6, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv6 hG with h_v15 in EoCases.__eo_to_smt_type.case_14 using hn_v1 hn_v2 hn_v4 hn_v5

theorem case_15_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_15_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_to_smt_type.case_15
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Set.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type.case_15
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with ih.eo__24eo_5fto_5fsmt_5ftype s2 v2 _ hinv2 h64 (hG.rem hrem) h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eSet.construct s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftypeof_5fguard s4 v4 v6 _ _ hinv4 h64 (hG.rem hrem) h_v4 h_v6 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v7 in EoCases.__eo_to_smt_type.case_15 using hn_v1 hn_v2

theorem case_16_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_16_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type.case_16 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_type.case_16 using

theorem cases_0_0_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_0_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_0 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_1 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_2 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_0 x_a0] ++ [EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using
  group_step with case_1_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0] ++ [EoCases.__eo_to_smt_type.case_1 x_a0] ++ [EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hl_0
  group_step with case_2_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0] ++ [EoCases.__eo_to_smt_type.case_2 x_a0] ++ [EoCases.__eo_to_smt_type.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hl_0 hl_1
  group_step with case_3_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0] ++ [EoCases.__eo_to_smt_type.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_1_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_4 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_5 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_6 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_4 x_a0] ++ [EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using
  group_step with case_5_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [EoCases.__eo_to_smt_type.case_4 x_a0] ++ [EoCases.__eo_to_smt_type.case_5 x_a0] ++ [EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hl_4
  group_step with case_6_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0] ++ [EoCases.__eo_to_smt_type.case_6 x_a0] ++ [EoCases.__eo_to_smt_type.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hl_4 hl_5
  group_step with case_7_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] = [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0] ++ [EoCases.__eo_to_smt_type.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_2_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_8 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_9 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_10 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_8 x_a0] ++ [EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using
  group_step with case_9_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_8 x_a0] ++ [EoCases.__eo_to_smt_type.case_9 x_a0] ++ [EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hl_8
  group_step with case_10_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0] ++ [EoCases.__eo_to_smt_type.case_10 x_a0] ++ [EoCases.__eo_to_smt_type.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hl_8 hl_9
  group_step with case_11_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] = [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0] ++ [EoCases.__eo_to_smt_type.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_3_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_12 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_13 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_14 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_12 x_a0] ++ [EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using
  group_step with case_13_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [EoCases.__eo_to_smt_type.case_12 x_a0] ++ [EoCases.__eo_to_smt_type.case_13 x_a0] ++ [EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hl_12
  group_step with case_14_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0] ++ [EoCases.__eo_to_smt_type.case_14 x_a0] ++ [EoCases.__eo_to_smt_type.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hl_12 hl_13
  group_step with case_15_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0] ++ [EoCases.__eo_to_smt_type.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_0_4_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_16 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_16 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_16 x_a0] ++ [] from rfl)
    otherwise ⟨hl_16⟩ using
  group_none hinv1 hG with hl_16

theorem cases_1_0_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_0_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_0 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_1 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_2 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_3 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_4 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_5 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_6 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_7 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_8 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_9 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_10 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_11 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_12 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_13 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_14 x_a0 = none ∧ EoCases.__eo_to_smt_type.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] ++ [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using
  group_step with cases_0_1_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0] ++ [EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] ++ [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24eo_5fto_5fsmt_5ftype_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0] ++ [EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] ++ [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24eo_5fto_5fsmt_5ftype_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0] ++ [EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    cases_1_1_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_to_smt_type.case_16 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type.case_16 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_16 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_16 x_a0] ++ [] from rfl)
    otherwise ⟨hl_16⟩ using
  group_none hinv1 hG with hl_16

/-- logos's `__eo_to_smt_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_to_smt_type x_a0 =
      (firstSome [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0, EoCases.__eo_to_smt_type.case_16 x_a0] default) := by
  conv => lhs; unfold __eo_to_smt_type
  unfold EoCases.__eo_to_smt_type.case_0 EoCases.__eo_to_smt_type.case_1 EoCases.__eo_to_smt_type.case_2 EoCases.__eo_to_smt_type.case_3 EoCases.__eo_to_smt_type.case_4 EoCases.__eo_to_smt_type.case_5 EoCases.__eo_to_smt_type.case_6 EoCases.__eo_to_smt_type.case_7 EoCases.__eo_to_smt_type.case_8 EoCases.__eo_to_smt_type.case_9 EoCases.__eo_to_smt_type.case_10 EoCases.__eo_to_smt_type.case_11 EoCases.__eo_to_smt_type.case_12 EoCases.__eo_to_smt_type.case_13 EoCases.__eo_to_smt_type.case_14 EoCases.__eo_to_smt_type.case_15 EoCases.__eo_to_smt_type.case_16
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fto_5fsmt_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fto_5fsmt_5ftype
  have hG := Store.Grows.refl s
  body_group_step with cases_1_0_eo__24eo_5fto_5fsmt_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0, EoCases.__eo_to_smt_type.case_16 x_a0] = [] ++ [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] ++ [EoCases.__eo_to_smt_type.case_16 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using
  body_group_step with cases_1_1_eo__24eo_5fto_5fsmt_5ftype_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0, EoCases.__eo_to_smt_type.case_16 x_a0] = [EoCases.__eo_to_smt_type.case_0 x_a0, EoCases.__eo_to_smt_type.case_1 x_a0, EoCases.__eo_to_smt_type.case_2 x_a0, EoCases.__eo_to_smt_type.case_3 x_a0, EoCases.__eo_to_smt_type.case_4 x_a0, EoCases.__eo_to_smt_type.case_5 x_a0, EoCases.__eo_to_smt_type.case_6 x_a0, EoCases.__eo_to_smt_type.case_7 x_a0, EoCases.__eo_to_smt_type.case_8 x_a0, EoCases.__eo_to_smt_type.case_9 x_a0, EoCases.__eo_to_smt_type.case_10 x_a0, EoCases.__eo_to_smt_type.case_11 x_a0, EoCases.__eo_to_smt_type.case_12 x_a0, EoCases.__eo_to_smt_type.case_13 x_a0, EoCases.__eo_to_smt_type.case_14 x_a0, EoCases.__eo_to_smt_type.case_15 x_a0] ++ [EoCases.__eo_to_smt_type.case_16 x_a0] ++ [] from rfl)
    otherwise ⟨hl_16⟩ using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  body_stuck hinv2 hG using hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 in EoCases.__eo_to_smt_type.case_0 EoCases.__eo_to_smt_type.case_1 EoCases.__eo_to_smt_type.case_2 EoCases.__eo_to_smt_type.case_3 EoCases.__eo_to_smt_type.case_4 EoCases.__eo_to_smt_type.case_5 EoCases.__eo_to_smt_type.case_6 EoCases.__eo_to_smt_type.case_7 EoCases.__eo_to_smt_type.case_8 EoCases.__eo_to_smt_type.case_9 EoCases.__eo_to_smt_type.case_10 EoCases.__eo_to_smt_type.case_11 EoCases.__eo_to_smt_type.case_12 EoCases.__eo_to_smt_type.case_13 EoCases.__eo_to_smt_type.case_14 EoCases.__eo_to_smt_type.case_15 EoCases.__eo_to_smt_type.case_16 splitting x_a0

theorem eo__24eo_5fto_5fsmt_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fto_5fsmt_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 772#u32 _ [a0] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftype s1 a0) (fun s' t => Represents.rep s' t (__eo_to_smt_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_772 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_772 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type_tuple.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type_tuple.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple more_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_to_smt_type_tuple.case_0
  pat_destruct CtorSpec.eo__24emb_5fdd_2econs.destruct h_v2 as ⟨v4, x_v4, h_v4⟩ ⟨v5, x_v5, h_v5⟩ ⟨v6, x_v6, h_v6⟩ else hinv hG in EoCases.__eo_to_smt_type_tuple.case_0
  pat_destruct CtorSpec.eo__24emb_5fdt_2esum.destruct h_v5 as ⟨v8, x_v8, h_v8⟩ ⟨v9, x_v9, h_v9⟩ else hinv hG in EoCases.__eo_to_smt_type_tuple.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s e_v10 (by rw [he_v10]; exact empty_args) hinv h64 as ⟨v10, s1, hinv1, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9
  pat_same v9 v10 with h_v9 h_v10 using hinv1 else hinv1 hG in EoCases.__eo_to_smt_type_tuple.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__24emb_5fdd_2enil.construct s1 e_v11 (by rw [he_v11]; exact empty_args) hinv1 h64 as ⟨v11, s2, hinv2, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10
  pat_same v6 v11 with h_v6 h_v11 using hinv2 else hinv2 hG in EoCases.__eo_to_smt_type_tuple.case_0
  step as ⟨e_v12, he_v12⟩
  simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v12, s3, hinv3, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11
  replace h_v12 := Represents.rep_of_eq h_v12 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v12]; decide)
  step as ⟨e_v13, he_v13⟩
  store_step with Store.native_spec_streq s3 e_v13 (by rw [he_v13]; rfl) h_v1 h_v12 hinv3 h64 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12
  rw [← Bridge.native_streq] at h_v13
  step as ⟨e_v14, he_v14⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.raw_str_vec_spec s4 _ _ rfl hinv4 h64 as ⟨v14, s5, hinv5, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  replace h_v14 := Represents.rep_of_eq h_v14 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v14]; decide)
  step as ⟨e_v15, he_v15⟩
  store_step with Store.native_spec_streq s5 e_v15 (by rw [he_v15]; rfl) h_v4 h_v14 hinv5 h64 as ⟨v15, s6, hinv6, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  rw [← Bridge.native_streq] at h_v15
  step as ⟨e_v16, he_v16⟩
  store_step with Store.native_spec_and s6 e_v16 (by rw [he_v16]; rfl) h_v13 h_v15 hinv6 h64 as ⟨v16, s7, hinv7, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  rw [← Bridge.native_and] at h_v16
  store_step with ih.eo__24smtx_5ftype_5fwf_5fcomponent s7 a0 _ hinv7 h64 (hG.rem hrem) h_a0 as ⟨v17, s8, hinv8, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  step as ⟨e_v18, he_v18⟩
  store_step with Store.native_spec_and s8 e_v18 (by rw [he_v18]; rfl) h_v16 h_v17 hinv8 h64 as ⟨v18, s9, hinv9, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  rw [← Bridge.native_and] at h_v18
  have h_ite_v26 := (show if_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple s9 v18 a0 v8 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    rcases Store.boolean_value_native h_v18 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
    · ite_branch hbv_19
      step as ⟨e_v19, he_v19⟩
      try simp only [eostring.EoString.from_code_points, Std.bind_ok]
      store_step with Store.raw_str_vec_spec s9 _ _ rfl hinv9 h64 as ⟨v19, s10, hinv10, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      replace h_v19 := Represents.rep_of_eq h_v19 (y := SmtEval.native_string_lit "@Tuple") (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v19]; decide)
      step as ⟨e_v20, he_v20⟩
      store_step with CtorSpec.eo__24emb_5fdtc_2econs.construct s10 e_v20 (by rw [he_v20]; rfl) h_a0 h_v8 hinv10 h64 as ⟨v20, s11, hinv11, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo__24emb_5fdt_2enull.construct s11 e_v21 (by rw [he_v21]; exact empty_args) hinv11 h64 as ⟨v21, s12, hinv12, h_v21⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      step as ⟨e_v22, he_v22⟩
      store_step with CtorSpec.eo__24emb_5fdt_2esum.construct s12 e_v22 (by rw [he_v22]; rfl) h_v20 h_v21 hinv12 h64 as ⟨v22, s13, hinv13, h_v22⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      store_step with ih.eo__24eo_5fto_5fsmt_5ftuple_5fdecl s13 v22 _ hinv13 h64 (hG.rem hrem) h_v22 as ⟨v23, s14, hinv14, h_v23⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      step as ⟨e_v24, he_v24⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eDatatype.construct s14 e_v24 (by rw [he_v24]; rfl) h_v19 h_v23 hinv14 h64 as ⟨v24, s15, hinv15, h_v24⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
      ite_done hinv15 hG with (native_ite_true_rep _ hx_19 h_v24)
    · ite_branch hbv_19
      step as ⟨e_v25, he_v25⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s9 e_v25 (by rw [he_v25]; exact empty_args) hinv9 h64 as ⟨v25, s10, hinv10, h_v25⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      ite_done hinv10 hG with (native_ite_false_rep _ hx_19 h_v25))
  store_step with h_ite_v26 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv10 hG with h_v26 in EoCases.__eo_to_smt_type_tuple.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_type_tuple.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_type_tuple.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_type_tuple.case_1 using

/-- logos's `__eo_to_smt_type_tuple` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5ftype_5ftuple.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_to_smt_type_tuple x_a0 x_a1 =
      (firstSome [EoCases.__eo_to_smt_type_tuple.case_0 x_a0 x_a1, EoCases.__eo_to_smt_type_tuple.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_to_smt_type_tuple
  unfold EoCases.__eo_to_smt_type_tuple.case_0 EoCases.__eo_to_smt_type_tuple.case_1
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fto_5fsmt_5ftype_5ftuple s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_type_tuple x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5ftype_5ftuple.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fto_5fsmt_5ftype_5ftuple
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_to_smt_type_tuple.case_0 EoCases.__eo_to_smt_type_tuple.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5ftype_5ftuple.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fto_5fsmt_5ftype_5ftuple
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fto_5fsmt_5ftype_5ftuple s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_to_smt_type_tuple x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5ftype_5ftuple_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    case_0_eo__24eo_5fto_5fsmt_5fupdater_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_updater_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_updater_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fto_5fsmt_5fupdater_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtSel.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt_updater_rec.case_0
  pat_native_zero Store.native_pattern_nat_zero_spec s a1 h_a1 hinv h64 storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 in EoCases.__eo_to_smt_updater_rec.case_0
  case_done hinv1 hG with h_a4 in EoCases.__eo_to_smt_updater_rec.case_0 using

theorem case_1_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    case_1_eo__24eo_5fto_5fsmt_5fupdater_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_updater_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_updater_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fto_5fsmt_5fupdater_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eDtSel.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_to_smt_updater_rec.case_1
  pat_destruct_lit Store.native_pattern_succ_spec s a1 h_a1 hinv h64 as ⟨v6, x_v6, h_v6⟩ storing ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 in EoCases.__eo_to_smt_updater_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eDtSel.construct s1 e_v7 (by rw [he_v7]; rfl) h_v1 h_v2 h_v3 h_v4 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6
  store_step with ih.eo__24eo_5fto_5fsmt_5fupdater_5frec s2 v7 v6 a2 a3 a4 _ _ _ _ _ hinv2 h64 (hG.rem hrem) h_v7 h_v6 h_a2 h_a3 h_a4 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_nateq s3 e_v9 (by rw [he_v9]; rfl) h_v4 h_v6 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6 h_v7 h_v8
  rw [← Bridge.native_nateq] at h_v9
  have h_ite_v12 := (show if_0_eo__24eo_5fto_5fsmt_5fupdater_5frec s4 v9 a3 v1 v2 v3 v6 a2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fto_5fsmt_5fupdater_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_native h_v9 with ⟨hx_10, hbv_10⟩ | ⟨hx_10, hbv_10⟩
    · ite_branch hbv_10
      ite_done hinv4 hG with (native_ite_true_rep _ hx_10 h_a3)
    · ite_branch hbv_10
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eDtSel.construct s4 e_v10 (by rw [he_v10]; rfl) h_v1 h_v2 h_v3 h_v6 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s5 e_v11 (by rw [he_v11]; rfl) h_v10 h_a2 hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10
      ite_done hinv6 hG with (native_ite_false_rep _ hx_10 h_v11))
  store_step with h_ite_v12 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eApply.construct s5 e_v13 (by rw [he_v13]; rfl) h_v8 h_v12 hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v12
  case_done hinv6 hG with h_v13 in EoCases.__eo_to_smt_updater_rec.case_1 using

theorem case_2_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    case_2_eo__24eo_5fto_5fsmt_5fupdater_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_to_smt_updater_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_to_smt_updater_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fto_5fsmt_5fupdater_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  case_done hinv1 hG with h_v0 in EoCases.__eo_to_smt_updater_rec.case_2 using

/-- logos's `__eo_to_smt_updater_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fto_5fsmt_5fupdater_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_to_smt_updater_rec x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_to_smt_updater_rec.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_to_smt_updater_rec.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_to_smt_updater_rec.case_2 x_a0 x_a1 x_a2 x_a3 x_a4] default) := by
  conv => lhs; unfold __eo_to_smt_updater_rec
  unfold EoCases.__eo_to_smt_updater_rec.case_0 EoCases.__eo_to_smt_updater_rec.case_1 EoCases.__eo_to_smt_updater_rec.case_2
  logos_eq

theorem body_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fto_5fsmt_5fupdater_5frec s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_to_smt_updater_rec x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fto_5fsmt_5fupdater_5frec.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fto_5fsmt_5fupdater_5frec
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using
  case_step with case_1_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hc0
  case_step with case_2_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_to_smt_updater_rec.case_0 EoCases.__eo_to_smt_updater_rec.case_1 EoCases.__eo_to_smt_updater_rec.case_2 splitting x_a0 x_a1 x_a2 x_a3 x_a4

theorem eo__24eo_5fto_5fsmt_5fupdater_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fto_5fsmt_5fupdater_5frec.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fto_5fsmt_5fupdater_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 776#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24eo_5fto_5fsmt_5fupdater_5frec s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_to_smt_updater_rec x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_776 hsem
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
      exact ProgramSem.to_776 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fto_5fsmt_5fupdater_5frec_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_2b s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_plus.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_plus.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_2b
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__eo_typeof_plus.case_0
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_req_v2 := (show requires_0_eo__24eo_5ftypeof_5f_2b s2 v0 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5f_2b
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    req_done hinv2 hG with h_a0 using hq_v0)
  store_step with h_req_v2 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof_plus.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_plus` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_2b.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_plus x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_plus.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_plus
  unfold EoCases.__eo_typeof_plus.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_2b s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_plus x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_2b.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_2b
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_2b_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_plus.case_0

theorem eo__24eo_5ftypeof_5f_2b_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_2b.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_2b
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_2b s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_plus x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_2b_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_2f_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_2f s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_qdiv.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_qdiv.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_2f
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__eo_typeof_qdiv.case_0
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_req_v3 := (show requires_0_eo__24eo_5ftypeof_5f_2f s2 v0 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5f_2f
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    step as ⟨e_v2, he_v2⟩
    store_step with CtorSpec.eo_Real.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
    req_done hinv3 hG with h_v2 using hq_v0)
  store_step with h_req_v3 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv4 hG with h_v3 in EoCases.__eo_typeof_qdiv.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_qdiv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_2f.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_qdiv x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_qdiv.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_qdiv
  unfold EoCases.__eo_typeof_qdiv.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_2f_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_2f s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_qdiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_2f.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_2f
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_2f_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_qdiv.case_0

theorem eo__24eo_5ftypeof_5f_2f_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_2f.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_2f
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_2f s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_qdiv x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_2f_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_3c_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_3c s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_lt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_lt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_3c
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__eo_typeof_lt.case_0
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  have h_req_v3 := (show requires_0_eo__24eo_5ftypeof_5f_3c s2 v0 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5f_3c
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    step as ⟨e_v2, he_v2⟩
    store_step with CtorSpec.eo__24emb_5fBool.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
    req_done hinv3 hG with h_v2 using hq_v0)
  store_step with h_req_v3 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv4 hG with h_v3 in EoCases.__eo_typeof_lt.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_lt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_3c.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_lt x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_lt.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_lt
  unfold EoCases.__eo_typeof_lt.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_3c_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_3c s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_lt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_3c.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_3c
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_3c_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_lt.case_0

theorem eo__24eo_5ftypeof_5f_3c_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_3c.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_3c
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_3c s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_lt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_3c_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  pat_same a1 a0 with h_a1 h_a0 using hinv else hinv hG in EoCases.__eo_typeof_eq.case_0
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_typeof_eq.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_3d.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_eq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_eq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_eq
  unfold EoCases.__eo_typeof_eq.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_3d_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_3d s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_3d.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_3d
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_3d_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_eq.case_0

theorem eo__24eo_5ftypeof_5f_3d_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_3d.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_3d
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_3d s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_3d_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40Pair_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40Pair s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_Pair.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_Pair.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40Pair
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_Pair.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at__at_Pair.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof__at__at_Pair.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof__at__at_Pair` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40Pair.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_Pair x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_Pair.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_Pair
  unfold EoCases.__eo_typeof__at__at_Pair.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40Pair_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40Pair s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_Pair x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40Pair.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40Pair
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40Pair_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_Pair.case_0

theorem eo__24eo_5ftypeof_5f_40_40Pair_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40Pair.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40Pair
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40Pair s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_Pair x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40Pair_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2econs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_TypedList_cons.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_TypedList_cons.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at__at_TypedList_cons.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_TypedList_cons.case_0
  pat_same v2 a0 with h_v2 h_a0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_TypedList_cons.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 a0 _ _ hinv2 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof__at__at_TypedList_cons.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

/-- logos's `__eo_typeof__at__at_TypedList_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40TypedList_2econs.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_TypedList_cons x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_TypedList_cons.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_TypedList_cons
  unfold EoCases.__eo_typeof__at__at_TypedList_cons.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_TypedList_cons x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40TypedList_2econs.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2econs_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_TypedList_cons.case_0

theorem eo__24eo_5ftypeof_5f_40_40TypedList_2econs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40TypedList_2econs.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40TypedList_2econs
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_TypedList_cons x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40TypedList_2econs_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2enil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2enil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_TypedList_nil.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_TypedList_nil.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2enil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_TypedList_nil.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof__at__at_TypedList_nil.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof__at__at_TypedList_nil` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40TypedList_2enil.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_TypedList_nil x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_TypedList_nil.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_TypedList_nil
  unfold EoCases.__eo_typeof__at__at_TypedList_nil.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_TypedList_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40TypedList_2enil.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40TypedList_2enil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_TypedList_nil.case_0

theorem eo__24eo_5ftypeof_5f_40_40TypedList_2enil_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40TypedList_2enil.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40TypedList_2enil
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_TypedList_nil x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40TypedList_2enil_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40aci_5fsorted_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40aci_5fsorted s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_aci_sorted.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_aci_sorted.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40aci_5fsorted
  have hG := Store.Grows.refl s
  case_done hinv hG with h_a1 in EoCases.__eo_typeof__at__at_aci_sorted.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof__at__at_aci_sorted` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40aci_5fsorted.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_aci_sorted x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_aci_sorted.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_aci_sorted
  unfold EoCases.__eo_typeof__at__at_aci_sorted.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_aci_sorted x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40aci_5fsorted.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40aci_5fsorted_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_aci_sorted.case_0

theorem eo__24eo_5ftypeof_5f_40_40aci_5fsorted_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40aci_5fsorted.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40aci_5fsorted
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_aci_sorted x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40aci_5fsorted_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40mon_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40mon s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_mon.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_mon.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40mon
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_mon.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Real.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at__at_mon.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__40_40Monomial.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof__at__at_mon.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof__at__at_mon` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40mon.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_mon x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_mon.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_mon
  unfold EoCases.__eo_typeof__at__at_mon.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40mon_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40mon s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_mon x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40mon.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40mon
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40mon_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_mon.case_0

theorem eo__24eo_5ftypeof_5f_40_40mon_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40mon.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40mon
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40mon s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_mon x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40mon_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40pair_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40pair s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_pair.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_pair.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40pair
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40Pair.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof__at__at_pair.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof__at__at_pair` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40pair.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_pair x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_pair.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_pair
  unfold EoCases.__eo_typeof__at__at_pair.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40pair_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40pair s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_pair x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40pair.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40pair
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40pair_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_pair.case_0

theorem eo__24eo_5ftypeof_5f_40_40pair_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40pair.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40pair
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40pair s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_pair x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40pair_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40_40poly_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40_40poly s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at__at_poly.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at__at_poly.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40_40poly
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40Monomial.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_poly.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40Polynomial.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at__at_poly.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__40_40Polynomial.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof__at__at_poly.case_0 using hn_a0 hn_a1

/-- logos's `__eo_typeof__at__at_poly` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40_40poly.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at__at_poly x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at__at_poly.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at__at_poly
  unfold EoCases.__eo_typeof__at__at_poly.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40_40poly_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40_40poly s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at__at_poly x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40_40poly.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40_40poly
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40_40poly_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at__at_poly.case_0

theorem eo__24eo_5ftypeof_5f_40_40poly_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40_40poly.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40_40poly
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40_40poly s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at__at_poly x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40_40poly_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_array_deq_diff.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_array_deq_diff.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Array.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_Array.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_same v12 v5 with h_v12 h_v5 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_same v9 v2 with h_v9 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  case_done hinv2 hG with h_v5 in EoCases.__eo_typeof__at_array_deq_diff.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_typeof__at_array_deq_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_array_deq_diff x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_array_deq_diff.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_array_deq_diff
  unfold EoCases.__eo_typeof__at_array_deq_diff.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_array_deq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_array_deq_diff.case_0

theorem eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_array_deq_diff x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40array_5fdeq_5fdiff_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40bit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40bit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_bit.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_bit.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40bit
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_bit.case_0
  pat_unapply h_a1 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_bit.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_bit.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof__at_bit.case_0 using hn_a0 hn_a1 hn_v2 hn_v3

/-- logos's `__eo_typeof__at_bit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40bit.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_bit x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_bit.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_bit
  unfold EoCases.__eo_typeof__at_bit.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40bit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40bit s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_bit x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40bit.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40bit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40bit_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_bit.case_0

theorem eo__24eo_5ftypeof_5f_40bit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40bit.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40bit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40bit s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_bit x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40bit_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40bvsize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40bvsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_bvsize.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_bvsize.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40bvsize
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_bvsize.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_bvsize.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_typeof__at_bvsize.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_typeof__at_bvsize` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40bvsize.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof__at_bvsize x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_bvsize.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_bvsize
  unfold EoCases.__eo_typeof__at_bvsize.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40bvsize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5f_40bvsize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_bvsize x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40bvsize.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5f_40bvsize
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40bvsize_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof__at_bvsize.case_0

theorem eo__24eo_5ftypeof_5f_40bvsize_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40bvsize.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5f_40bvsize
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40bvsize s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof__at_bvsize x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40bvsize_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40const_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40const s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_const.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_const.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40const
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_const.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_const.case_0
  case_done hinv2 hG with h_a2 in EoCases.__eo_typeof__at_const.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_typeof__at_const` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40const.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_typeof__at_const x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_const.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_const
  unfold EoCases.__eo_typeof__at_const.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40const_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5ftypeof_5f_40const s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_const x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40const.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5ftypeof_5f_40const
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40const_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_typeof__at_const.case_0

theorem eo__24eo_5ftypeof_5f_40const_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40const.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5ftypeof_5f_40const
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40const s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_typeof__at_const x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40const_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40div_5fby_5fzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40div_5fby_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_div_by_zero.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_div_by_zero.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40div_5fby_5fzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_div_by_zero.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Real.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof__at_div_by_zero.case_0 using hn_a0

/-- logos's `__eo_typeof__at_div_by_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40div_5fby_5fzero.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof__at_div_by_zero x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_div_by_zero.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_div_by_zero
  unfold EoCases.__eo_typeof__at_div_by_zero.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_div_by_zero x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40div_5fby_5fzero.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40div_5fby_5fzero_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof__at_div_by_zero.case_0

theorem eo__24eo_5ftypeof_5f_40div_5fby_5fzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40div_5fby_5fzero.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5f_40div_5fby_5fzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof__at_div_by_zero x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40div_5fby_5fzero_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
