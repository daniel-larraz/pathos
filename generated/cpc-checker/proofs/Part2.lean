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

theorem case_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__contains_atomic_term_list_free_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__contains_atomic_term_list_free_rec.case_0 x_a0 x_a1 x_a2 = some (__contains_atomic_term_list_free_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__contains_atomic_term_list_free_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__contains_atomic_term_list_free_rec.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__contains_atomic_term_list_free_rec.case_0
  pat_unapply h_v5 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__contains_atomic_term_list_free_rec.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv else hinv hG in EoCases.__contains_atomic_term_list_free_rec.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v12 (by rw [he_v12]; exact empty_args) hinv h64 as ⟨v12, s1, hinv1, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv1 else hinv1 hG in EoCases.__contains_atomic_term_list_free_rec.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s3 v14 v11 _ _ hinv3 h64 h_v14 h_v11 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s4 v15 v8 _ _ hinv4 h64 h_v15 h_v8 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s5 e_v17 (by rw [he_v17]; rfl) h_v13 h_v16 h_a2 hinv5 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  case_again hinv6 hG with h_v2 h_a1 h_v17 in EoCases.__contains_atomic_term_list_free_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v10 hn_v11

theorem case_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__contains_atomic_term_list_free_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__contains_atomic_term_list_free_rec.case_1 x_a0 x_a1 x_a2 = some (__contains_atomic_term_list_free_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__contains_atomic_term_list_free_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__contains_atomic_term_list_free_rec.case_1
  store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s v1 a1 a2 _ _ _ hinv h64 hrem h_v1 h_a1 h_a2 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  have h_ite_v6 := (show if_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s1 v3 v2 a1 a2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_v3 with ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩ | ⟨hx_4, hbv_4⟩
    · ite_branch hbv_4
      store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (eo_ite_true_rep _ hx_4 h_v4)
    · ite_branch hbv_4
      store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s1 v2 a1 a2 _ _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 h_a2 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
      ite_done hinv2 hG with (eo_ite_false_rep _ hx_4 h_v5)
    · ite_branch hbv_4
      ite_stuck hinv1 hG with hx_4)
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v6 in EoCases.__contains_atomic_term_list_free_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__contains_atomic_term_list_free_rec.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__contains_atomic_term_list_free_rec.case_2 x_a0 x_a1 x_a2 = some (__contains_atomic_term_list_free_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__contains_atomic_term_list_free_rec.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fVar.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__contains_atomic_term_list_free_rec.case_2
  obtain ⟨hn_v1, hn_v2⟩ := CtorSpec.eo__24emb_5fVar.fields_ne_stuck hinv h_a0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v2 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_a1 h_v4 hinv2 h64 (hG.rem hrem) (by not_left_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_is_neg s3 e_v6 (by rw [he_v6]; rfl) h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5
  have h_ite_v12 := (show if_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s4 v6 v1 v2 a2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      step as ⟨e_v8, he_v8⟩
      store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s4 e_v8 (by rw [he_v8]; exact empty_args) hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v9, he_v9⟩
      store_step with CtorSpec.eo__24emb_5fVar.construct s5 e_v9 (by rw [he_v9]; rfl) h_v1 h_v2 hinv5 h64 as ⟨v9, s6, hinv6, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v8
      step as ⟨e_v10, he_v10⟩
      store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s6 e_v10 (by rw [he_v10]; rfl) h_v8 h_a2 h_v9 hinv6 h64 (hG.rem hrem) (by not_left_tac) as ⟨v10, s7, hinv7, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v8 h_v9
      step as ⟨e_v11, he_v11⟩
      store_step with Store.builtin_spec_is_neg s7 e_v11 (by rw [he_v11]; rfl) h_v10 hinv7 h64 as ⟨v11, s8, hinv8, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_7 h_v11)
    · ite_branch hbv_7
      ite_stuck hinv4 hG with hx_7)
  store_step with h_ite_v12 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv5 hG with h_v12 in EoCases.__contains_atomic_term_list_free_rec.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_3_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__contains_atomic_term_list_free_rec.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__contains_atomic_term_list_free_rec.case_3 x_a0 x_a1 x_a2 = some (__contains_atomic_term_list_free_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__contains_atomic_term_list_free_rec.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  store_step with ih.eo__24is_5fclosed_5frec s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  have h_req_v4 := (show requires_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s3 v1 v2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v1 v2 with h_v1 h_v2 using hinv3 hG
    req_stuck h_v1 as hq_v1 using hinv3 hG
    store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
    req_done hinv4 hG with h_v3 using hq_v1)
  store_step with h_req_v4 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv5 hG with h_v4 in EoCases.__contains_atomic_term_list_free_rec.case_3 using hn_a0 hn_a1 hn_a2

/-- logos's `__contains_atomic_term_list_free_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __contains_atomic_term_list_free_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__contains_atomic_term_list_free_rec.case_0 x_a0 x_a1 x_a2, EoCases.__contains_atomic_term_list_free_rec.case_1 x_a0 x_a1 x_a2, EoCases.__contains_atomic_term_list_free_rec.case_2 x_a0 x_a1 x_a2, EoCases.__contains_atomic_term_list_free_rec.case_3 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __contains_atomic_term_list_free_rec
  unfold EoCases.__contains_atomic_term_list_free_rec.case_0 EoCases.__contains_atomic_term_list_free_rec.case_1 EoCases.__contains_atomic_term_list_free_rec.case_2 EoCases.__contains_atomic_term_list_free_rec.case_3
  logos_eq

theorem step_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__contains_atomic_term_list_free_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __contains_atomic_term_list_free_rec x_a0 x_a1 x_a2 = __contains_atomic_term_list_free_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_step with case_2_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0 hc1
  round_step with case_3_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec n ih s4 a0 a1 a2 x_a0 x_a1 x_a2 hinv4 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2
  round_stuck hinv5 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 hc3 in EoCases.__contains_atomic_term_list_free_rec.case_0 EoCases.__contains_atomic_term_list_free_rec.case_1 EoCases.__contains_atomic_term_list_free_rec.case_2 EoCases.__contains_atomic_term_list_free_rec.case_3

theorem body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__contains_atomic_term_list_free_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__contains_atomic_term_list_free_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_loop
  step with step_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 59#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__contains_atomic_term_list_free_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_59 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_59 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
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

theorem case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_check_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eproven.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_invoke_cmd_check_proven.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_eq s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fpush_5fproven_5fcheck s1 v5 v4 v2 _ _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v4 h_v2 (by good_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_invoke_cmd_check_proven.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_invoke_cmd_check_proven.case_1 using

/-- logos's `__eo_invoke_cmd_check_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_invoke_cmd_check_proven x_a0 x_a1 =
      (firstSome [EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_invoke_cmd_check_proven
  unfold EoCases.__eo_invoke_cmd_check_proven.case_0 EoCases.__eo_invoke_cmd_check_proven.case_1
  logos_eq

theorem body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_invoke_cmd_check_proven.case_0 EoCases.__eo_invoke_cmd_check_proven.case_1 splitting x_a0 x_a1

theorem eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
  unfold eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__eo_invoke_cmd_step_pop y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_step_pop.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_invoke_cmd_step_pop.case_0
  store_step with ih.eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a2 a3 v4 a4 _ _ _ _ _ hinv h64 hrem h_a0 h_a2 h_a3 h_v4 h_a4 (by good_tac) as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fpush_5fproven s1 v5 v2 _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v2 (by good_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v2 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_invoke_cmd_step_pop.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__eo_invoke_cmd_step_pop y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_step_pop.case_1
  case_again hinv hG with h_a0 h_v2 h_a2 h_a3 h_a4 goods 2 in EoCases.__eo_invoke_cmd_step_pop.case_1 using

theorem case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some (__eo_invoke_cmd_step_pop y0 y1 y2 y3 y4)
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  case_done hinv1 hG with h_v0 in EoCases.__eo_invoke_cmd_step_pop.case_2 using

/-- logos's `__eo_invoke_cmd_step_pop` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd_5fstep_5fpop.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_invoke_cmd_step_pop.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_invoke_cmd_step_pop.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_invoke_cmd_step_pop.case_2 x_a0 x_a1 x_a2 x_a3 x_a4] default) := by
  conv => lhs; unfold __eo_invoke_cmd_step_pop
  unfold EoCases.__eo_invoke_cmd_step_pop.case_0 EoCases.__eo_invoke_cmd_step_pop.case_1 EoCases.__eo_invoke_cmd_step_pop.case_2
  logos_eq

theorem step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _) (u3 : Term) (y3 : _) (u4 : Term) (y4 : _), arr.val = [u0, u1, u2, u3, u4] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧ Represents.rep s' u3 y3 ∧ Represents.rep s' u4 y4 ∧ StateOK y0 ∧ StateOK y1 ∧
          __eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4 = __eo_invoke_cmd_step_pop y0 y1 y2 y3 y4
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd_5fstep_5fpop.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  round_step with case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using
  round_step with case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hc0
  round_step with case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s3 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 hbud using hc0 hc1
  round_stuck hinv4 hG using hc0 hc1 hc2 in EoCases.__eo_invoke_cmd_step_pop.case_0 EoCases.__eo_invoke_cmd_step_pop.case_1 EoCases.__eo_invoke_cmd_step_pop.case_2 splitting x_a0 x_a1 x_a2 x_a3 x_a4

theorem body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) (hg_a1 : StateOK x_a1) :
    body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 a3 a4 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 → Represents.rep s a3 x_a3 → Represents.rep s a4 x_a4 → StateOK x_a0 → StateOK x_a1 →
      body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 le_rfl hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 a3 a4 s x_a0 x_a1 x_a2 x_a3 x_a4 hk hinv hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
  unfold body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_loop
  step with step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, u3, y3, u4, y4, hnext, hrep0, hrep1, hrep2, hrep3, hrep4, hgood0, hgood1, heq⟩ := hr
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
      have hrec := ihl s1.budget (by omega) b0 b1 b2 b3 b4 s1 y0 y1 y2 y3 y4 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2  hrep3  hrep4  hgood0  hgood1
      unfold body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd_5fstep_5fpop.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0 hg_a1
  unfold eo__24eo_5finvoke_5fcmd_5fstep_5fpop
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_invoke_cmd_step_pop x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) hg_a0 hg_a1))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5fbool_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5fbool_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_bool_type.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_bool_type.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5fbool_5ftype
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5ftypeof s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_eq s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_bool_type.case_0 using hn_a0

/-- logos's `__eo_is_bool_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5fbool_5ftype.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_bool_type x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_bool_type.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_bool_type
  unfold EoCases.__eo_is_bool_type.case_0
  logos_eq

theorem body_eo__24eo_5fis_5fbool_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5fbool_5ftype s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_bool_type x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5fbool_5ftype.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5fbool_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5fbool_5ftype_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_bool_type.case_0

theorem eo__24eo_5fis_5fbool_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5fbool_5ftype.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5fbool_5ftype
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5fbool_5ftype s1 a0) (fun s' t => Represents.rep s' t (__eo_is_bool_type x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5fbool_5ftype_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_0
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_0 using hn_a0 hn_a1

theorem case_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_1
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_1
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_1 using hn_a0 hn_a1

theorem case_2_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_2
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_2
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_2 using hn_a0 hn_a1

theorem case_3_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_3_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_3
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5f_2b s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_3 using hn_a0 hn_a1

theorem case_4_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_4_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__2a.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_4
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5f_2a s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_4 using hn_a0 hn_a1

theorem case_5_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_5_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_concat.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_5
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_5
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_5 using hn_a0 hn_a1

theorem case_6_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_6_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvand.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_6
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvand s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_6 using hn_a0 hn_a1

theorem case_7_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_7_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_7
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvor s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_7 using hn_a0 hn_a1

theorem case_8_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_8_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvxor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_8
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvxor s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_8 using hn_a0 hn_a1

theorem case_9_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_9_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvadd.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_9
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvadd s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_9 using hn_a0 hn_a1

theorem case_10_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_10_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvmul.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_10
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvmul s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_10 using hn_a0 hn_a1

theorem case_11_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_11_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_11
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_11
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_11 using hn_a0 hn_a1

theorem case_12_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_12_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_12
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_12 using hn_a0 hn_a1

theorem case_13_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_13_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_13
  pat_unapply h_a1 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_13
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_13
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_is_list_nil.case_13
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_is_list_nil.case_13 using hn_a0 hn_a1 hn_v2 hn_v3

theorem case_14_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_14_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_14
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2eall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_14
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_14 using hn_a0 hn_a1

theorem case_15_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_15_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_15
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2enone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_15
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_15 using hn_a0 hn_a1

theorem case_16_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_16_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_16
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_UnitTuple.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_16
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_16 using hn_a0 hn_a1

theorem case_17_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_17_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_17
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_17
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_17 using hn_a0 hn_a1

theorem case_18_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_18_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_18_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40poly.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_18
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40poly_2ezero.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_18
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_18 using hn_a0 hn_a1

theorem case_19_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_19_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_19_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_19
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_19
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_19 using hn_a0 hn_a1

theorem case_20_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_20_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_20_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_is_list_nil.case_20 using hn_a0 hn_a1

theorem cases_0_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1
  group_step with case_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_1 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hl_0
  group_step with case_2_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_2 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hl_0 hl_1
  group_step with case_3_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1
  group_step with case_5_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_5 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hl_4
  group_step with case_6_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_6 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hn_a1 hl_4 hl_5
  group_step with case_7_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hn_a1 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0 hn_a1
  group_step with case_9_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_9 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hn_a1 hl_8
  group_step with case_10_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_10 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] from rfl)
    otherwise ⟨hl_10⟩ using hn_a0 hn_a1 hl_8 hl_9
  group_step with case_11_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hn_a0 hn_a1 hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_3_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_12⟩ using hn_a0 hn_a1
  group_step with case_13_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_13 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_13⟩ using hn_a0 hn_a1 hl_12
  group_step with case_14_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_14 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_14⟩ using hn_a0 hn_a1 hl_12 hl_13
  group_step with case_15_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hn_a0 hn_a1 hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_4_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] from rfl)
    otherwise ⟨hl_16⟩ using hn_a0 hn_a1
  group_step with case_17_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_17 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] from rfl)
    otherwise ⟨hl_17⟩ using hn_a0 hn_a1 hl_16
  group_step with case_18_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_18 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] from rfl)
    otherwise ⟨hl_18⟩ using hn_a0 hn_a1 hl_16 hl_17
  group_step with case_19_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_19⟩ using hn_a0 hn_a1 hl_16 hl_17 hl_18
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19⟩

theorem cases_0_5_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_5_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_5_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_20_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_20⟩ using hn_a0 hn_a1
  group_none hinv1 hG with hl_20

theorem cases_1_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_1_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1
  group_step with cases_0_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_1_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19⟩ using hn_a0 hn_a1
  group_step with cases_0_5_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_20⟩ using hn_a0 hn_a1 hl_16 hl_17 hl_18 hl_19
  group_none hinv2 hG with ⟨hl_16, hl_17, hl_18, hl_19, hl_20⟩

/-- logos's `__eo_is_list_nil` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_is_list_nil x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil
  unfold EoCases.__eo_is_list_nil.case_0 EoCases.__eo_is_list_nil.case_1 EoCases.__eo_is_list_nil.case_2 EoCases.__eo_is_list_nil.case_3 EoCases.__eo_is_list_nil.case_4 EoCases.__eo_is_list_nil.case_5 EoCases.__eo_is_list_nil.case_6 EoCases.__eo_is_list_nil.case_7 EoCases.__eo_is_list_nil.case_8 EoCases.__eo_is_list_nil.case_9 EoCases.__eo_is_list_nil.case_10 EoCases.__eo_is_list_nil.case_11 EoCases.__eo_is_list_nil.case_12 EoCases.__eo_is_list_nil.case_13 EoCases.__eo_is_list_nil.case_14 EoCases.__eo_is_list_nil.case_15 EoCases.__eo_is_list_nil.case_16 EoCases.__eo_is_list_nil.case_17 EoCases.__eo_is_list_nil.case_18 EoCases.__eo_is_list_nil.case_19 EoCases.__eo_is_list_nil.case_20
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  body_group_step with cases_1_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hn_a1
  body_group_step with cases_1_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19, hl_20⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  body_stuck hinv2 hG using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 in EoCases.__eo_is_list_nil.case_0 EoCases.__eo_is_list_nil.case_1 EoCases.__eo_is_list_nil.case_2 EoCases.__eo_is_list_nil.case_3 EoCases.__eo_is_list_nil.case_4 EoCases.__eo_is_list_nil.case_5 EoCases.__eo_is_list_nil.case_6 EoCases.__eo_is_list_nil.case_7 EoCases.__eo_is_list_nil.case_8 EoCases.__eo_is_list_nil.case_9 EoCases.__eo_is_list_nil.case_10 EoCases.__eo_is_list_nil.case_11 EoCases.__eo_is_list_nil.case_12 EoCases.__eo_is_list_nil.case_13 EoCases.__eo_is_list_nil.case_14 EoCases.__eo_is_list_nil.case_15 EoCases.__eo_is_list_nil.case_16 EoCases.__eo_is_list_nil.case_17 EoCases.__eo_is_list_nil.case_18 EoCases.__eo_is_list_nil.case_19 EoCases.__eo_is_list_nil.case_20

theorem eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fis_5flist_5fnil
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5f_2a_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5f_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_mult.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_mult.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5f_2a
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_q s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v0
  replace h_v2 := Represents.rep_of_eq h_v2 (y := Eo.Term.Rational (SmtEval.native_mk_rational (1) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_is_eq s2 e_v3 (by rw [he_v3]; rfl) h_v0 h_v2 hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_is_list_nil_mult.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_mult` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5f_2a.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_mult x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_mult.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_mult
  unfold EoCases.__eo_is_list_nil_mult.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5f_2a_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5f_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_mult x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5f_2a.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5f_2a
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5f_2a_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_mult.case_0

theorem eo__24eo_5fis_5flist_5fnil_5f_2a_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5f_2a.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5f_2a
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5f_2a s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_mult x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5f_2a_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5f_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5f_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_plus.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_plus.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5f_2b
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_q s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v0
  replace h_v2 := Represents.rep_of_eq h_v2 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_is_eq s2 e_v3 (by rw [he_v3]; rfl) h_v0 h_v2 hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_is_list_nil_plus.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_plus` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5f_2b.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_plus x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_plus.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_plus
  unfold EoCases.__eo_is_list_nil_plus.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5f_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5f_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_plus x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5f_2b.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5f_2b
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5f_2b_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_plus.case_0

theorem eo__24eo_5fis_5flist_5fnil_5f_2b_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5f_2b.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5f_2b
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5f_2b s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_plus x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5f_2b_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 using hn_a0 hn_v1 hn_v2

theorem case_1_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_1 using hn_a0

/-- logos's `__eo_is_list_nil__at__at_TypedList_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil__at__at_TypedList_cons x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 x_a0, EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil__at__at_TypedList_cons
  unfold EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_1
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil__at__at_TypedList_cons x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_1

theorem eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil__at__at_TypedList_cons x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5fbvadd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5fbvadd s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_bvadd.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_bvadd.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5fbvadd
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_z s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_is_eq s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil_bvadd.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_bvadd` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5fbvadd.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_bvadd x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_bvadd.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_bvadd
  unfold EoCases.__eo_is_list_nil_bvadd.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5fbvadd_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5fbvadd s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvadd x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5fbvadd.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5fbvadd
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5fbvadd_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_bvadd.case_0

theorem eo__24eo_5fis_5flist_5fnil_5fbvadd_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5fbvadd.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5fbvadd
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5fbvadd s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_bvadd x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5fbvadd_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5fbvand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5fbvand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_bvand.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_bvand.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5fbvand
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_not s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_to_z s1 e_v1 (by rw [he_v1]; rfl) h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_is_eq s3 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__eo_is_list_nil_bvand.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_bvand` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5fbvand.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_bvand x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_bvand.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_bvand
  unfold EoCases.__eo_is_list_nil_bvand.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5fbvand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5fbvand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvand x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5fbvand.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5fbvand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5fbvand_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_bvand.case_0

theorem eo__24eo_5fis_5flist_5fnil_5fbvand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5fbvand.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5fbvand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5fbvand s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_bvand x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5fbvand_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5fbvmul_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5fbvmul s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_bvmul.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_bvmul.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5fbvmul
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_len s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_to_bin s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_is_eq s3 e_v3 (by rw [he_v3]; rfl) h_a0 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__eo_is_list_nil_bvmul.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_bvmul` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5fbvmul.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_bvmul x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_bvmul.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_bvmul
  unfold EoCases.__eo_is_list_nil_bvmul.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5fbvmul_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5fbvmul s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvmul x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5fbvmul.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5fbvmul
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5fbvmul_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_bvmul.case_0

theorem eo__24eo_5fis_5flist_5fnil_5fbvmul_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5fbvmul.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5fbvmul
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5fbvmul s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_bvmul x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5fbvmul_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5fbvor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5fbvor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_bvor.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_bvor.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5fbvor
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_z s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_is_eq s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil_bvor.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_bvor` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5fbvor.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_bvor x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_bvor.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_bvor
  unfold EoCases.__eo_is_list_nil_bvor.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5fbvor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5fbvor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvor x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5fbvor.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5fbvor
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5fbvor_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_bvor.case_0

theorem eo__24eo_5fis_5flist_5fnil_5fbvor_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5fbvor.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5fbvor
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5fbvor s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_bvor x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5fbvor_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5fbvxor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5fbvxor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_bvxor.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_bvxor.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5fbvxor
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_z s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_is_eq s2 e_v2 (by rw [he_v2]; rfl) h_v0 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil_bvxor.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_bvxor` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5fbvxor.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_bvxor x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_bvxor.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_bvxor
  unfold EoCases.__eo_is_list_nil_bvxor.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5fbvxor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5fbvxor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_bvxor x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5fbvxor.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5fbvxor
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5fbvxor_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_bvxor.case_0

theorem eo__24eo_5fis_5flist_5fnil_5fbvxor_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5fbvxor.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5fbvxor
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5fbvxor s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_bvxor x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5fbvxor_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_str_concat.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_str_concat.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo_seq_2eempty.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_is_list_nil_str_concat.case_0
  obtain hn_v1 := CtorSpec.eo_seq_2eempty.fields_ne_stuck hinv h_a0
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_is_list_nil_str_concat.case_0 using hn_a0 hn_v1

theorem case_1_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_str_concat.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_str_concat.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b
  have hG := Store.Grows.refl s
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s _ _ rfl hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_eq s1 e_v1 (by rw [he_v1]; rfl) h_a0 h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil_str_concat.case_1 using hn_a0

/-- logos's `__eo_is_list_nil_str_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_str_concat x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_str_concat.case_0 x_a0, EoCases.__eo_is_list_nil_str_concat.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_str_concat
  unfold EoCases.__eo_is_list_nil_str_concat.case_0 EoCases.__eo_is_list_nil_str_concat.case_1
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_str_concat x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__eo_is_list_nil_str_concat.case_0 EoCases.__eo_is_list_nil_str_concat.case_1

theorem eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_str_concat x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
