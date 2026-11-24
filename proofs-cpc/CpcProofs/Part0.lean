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

theorem case_0_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_normalize_lit.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_normalize_lit.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  store_step with Store.apply_rep s2 v12 v13 _ _ hinv2 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13
  store_step with Store.apply_rep s3 v14 v10 _ _ hinv3 h64 h_v14 h_v10 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14
  case_done hinv4 hG with h_v15 in EoCases.__arith_normalize_lit.case_0 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_1_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_normalize_lit.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_normalize_lit.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  store_step with ih.eo__24arith_5frel_5fneg s1 v8 v9 v6 _ _ _ hinv1 h64 (hG.rem hrem) h_v8 h_v9 h_v6 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9
  case_done hinv2 hG with h_v10 in EoCases.__arith_normalize_lit.case_1 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v8 hn_v9

theorem case_2_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_normalize_lit.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_normalize_lit.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_2
  store_step with Store.apply_rep s v4 v5 _ _ hinv h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with Store.apply_rep s1 v6 v2 _ _ hinv1 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv2 hG with h_v7 in EoCases.__arith_normalize_lit.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__arith_normalize_lit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5fnormalize_5flit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __arith_normalize_lit x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_normalize_lit.case_0 x_a0, EoCases.__arith_normalize_lit.case_1 x_a0, EoCases.__arith_normalize_lit.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __arith_normalize_lit
  unfold EoCases.__arith_normalize_lit.case_0 EoCases.__arith_normalize_lit.case_1 EoCases.__arith_normalize_lit.case_2
  logos_eq

theorem body_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_normalize_lit x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5fnormalize_5flit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24arith_5fnormalize_5flit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24arith_5fnormalize_5flit_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  case_step with case_2_eo__24arith_5fnormalize_5flit_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hn_a0 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hc0 hc1 hc2 in EoCases.__arith_normalize_lit.case_0 EoCases.__arith_normalize_lit.case_1 EoCases.__arith_normalize_lit.case_2

theorem eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5fnormalize_5flit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24arith_5fnormalize_5flit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5fnormalize_5flit s1 a0) (fun s' t => Represents.rep s' t (__arith_normalize_lit x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5fnormalize_5flit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_2 using hn_a0 hn_a1 hn_a2

theorem case_3_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_3 using hn_a0 hn_a1 hn_a2

theorem case_4_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_4 using hn_a0 hn_a1 hn_a2

theorem cases_0_0_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2 = none ∧ EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2 = none ∧ EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2 = none ∧ EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5frel_5finv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [] ++ [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2
  group_step with case_1_eo__24arith_5frel_5finv_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hl_0
  group_step with case_2_eo__24arith_5frel_5finv_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1
  group_step with case_3_eo__24arith_5frel_5finv_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5frel_5finv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] = [] ++ [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2
  group_none hinv1 hG with hl_4

/-- logos's `__arith_rel_inv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5finv.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __arith_rel_inv x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_inv
  unfold EoCases.__arith_rel_inv.case_0 EoCases.__arith_rel_inv.case_1 EoCases.__arith_rel_inv.case_2 EoCases.__arith_rel_inv.case_3 EoCases.__arith_rel_inv.case_4
  logos_eq

theorem body_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_inv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5finv.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5frel_5finv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] = [] ++ [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2
  body_group_step with cases_0_1_eo__24arith_5frel_5finv_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3 hl_4 in EoCases.__arith_rel_inv.case_0 EoCases.__arith_rel_inv.case_1 EoCases.__arith_rel_inv.case_2 EoCases.__arith_rel_inv.case_3 EoCases.__arith_rel_inv.case_4

theorem eo__24arith_5frel_5finv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5finv.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24arith_5frel_5finv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5finv s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__arith_rel_inv x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5finv_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_2 using hn_a0 hn_a1 hn_a2

theorem case_3_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_3 using hn_a0 hn_a1 hn_a2

/-- logos's `__arith_rel_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5fneg.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __arith_rel_neg x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_neg.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_neg.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_neg.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_neg.case_3 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_neg
  unfold EoCases.__arith_rel_neg.case_0 EoCases.__arith_rel_neg.case_1 EoCases.__arith_rel_neg.case_2 EoCases.__arith_rel_neg.case_3
  logos_eq

theorem body_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_neg x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5fneg.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24arith_5frel_5fneg_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24arith_5frel_5fneg_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24arith_5frel_5fneg_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  case_step with case_3_eo__24arith_5frel_5fneg_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 hc3 in EoCases.__arith_rel_neg.case_0 EoCases.__arith_rel_neg.case_1 EoCases.__arith_rel_neg.case_2 EoCases.__arith_rel_neg.case_3

theorem eo__24arith_5frel_5fneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5fneg.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24arith_5frel_5fneg
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5fneg s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__arith_rel_neg x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5fneg_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_1_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_1 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_2_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_2 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_3_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_3 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_4_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_4 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_5_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_5_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_5
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_5
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_5 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_6_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_6_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_6
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_6
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_6 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_7_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_7_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_7
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_7
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_7 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_8_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_8_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_8
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_8
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_8 using hn_a0 hn_a1 hn_a2 hn_a3

theorem cases_0_0_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_1_eo__24arith_5frel_5fsum_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0
  group_step with case_2_eo__24arith_5frel_5fsum_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1
  group_step with case_3_eo__24arith_5frel_5fsum_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_5_eo__24arith_5frel_5fsum_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4
  group_step with case_6_eo__24arith_5frel_5fsum_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4 hl_5
  group_step with case_7_eo__24arith_5frel_5fsum_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_none hinv1 hG with hl_8

/-- logos's `__arith_rel_sum` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5fsum.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __arith_rel_sum x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_sum
  unfold EoCases.__arith_rel_sum.case_0 EoCases.__arith_rel_sum.case_1 EoCases.__arith_rel_sum.case_2 EoCases.__arith_rel_sum.case_3 EoCases.__arith_rel_sum.case_4 EoCases.__arith_rel_sum.case_5 EoCases.__arith_rel_sum.case_6 EoCases.__arith_rel_sum.case_7 EoCases.__arith_rel_sum.case_8
  logos_eq

theorem body_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_sum x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5fsum.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  body_group_step with cases_0_1_eo__24arith_5frel_5fsum_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24arith_5frel_5fsum_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 in EoCases.__arith_rel_sum.case_0 EoCases.__arith_rel_sum.case_1 EoCases.__arith_rel_sum.case_2 EoCases.__arith_rel_sum.case_3 EoCases.__arith_rel_sum.case_4 EoCases.__arith_rel_sum.case_5 EoCases.__arith_rel_sum.case_6 EoCases.__arith_rel_sum.case_7 EoCases.__arith_rel_sum.case_8

theorem eo__24arith_5frel_5fsum_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5fsum.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24arith_5frel_5fsum
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5fsum s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__arith_rel_sum x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5fsum_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3e.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_1_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_1 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_2_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_2 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_3_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3e.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_3 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_4_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_4 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_5_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_5_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_5
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_5
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_5 using hn_a0 hn_a1 hn_a2 hn_a3

theorem cases_0_0_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5frel_5ftrichotomy_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_1_eo__24arith_5frel_5ftrichotomy_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0
  group_step with case_2_eo__24arith_5frel_5ftrichotomy_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1
  group_step with case_3_eo__24arith_5frel_5ftrichotomy_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5frel_5ftrichotomy_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_5_eo__24arith_5frel_5ftrichotomy_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__arith_rel_trichotomy` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5ftrichotomy.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_trichotomy
  unfold EoCases.__arith_rel_trichotomy.case_0 EoCases.__arith_rel_trichotomy.case_1 EoCases.__arith_rel_trichotomy.case_2 EoCases.__arith_rel_trichotomy.case_3 EoCases.__arith_rel_trichotomy.case_4 EoCases.__arith_rel_trichotomy.case_5
  logos_eq

theorem body_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5ftrichotomy.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5frel_5ftrichotomy_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  body_group_step with cases_0_1_eo__24arith_5frel_5ftrichotomy_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__arith_rel_trichotomy.case_0 EoCases.__arith_rel_trichotomy.case_1 EoCases.__arith_rel_trichotomy.case_2 EoCases.__arith_rel_trichotomy.case_3 EoCases.__arith_rel_trichotomy.case_4 EoCases.__arith_rel_trichotomy.case_5

theorem eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5ftrichotomy.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24arith_5frel_5ftrichotomy
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5ftrichotomy s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5ftrichotomy_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_and.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_and.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__bv_bitblast_binary_app.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_or.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_or.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__bv_bitblast_binary_app.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_xor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__bv_bitblast_binary_app.case_2 using hn_a0 hn_a1 hn_a2

theorem case_3_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__bv_bitblast_binary_app.case_3 using hn_a0 hn_a1 hn_a2

/-- logos's `__bv_bitblast_binary_app` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fbinary_5fapp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_binary_app x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_binary_app.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_binary_app.case_1 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_binary_app.case_2 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_binary_app.case_3 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_binary_app
  unfold EoCases.__bv_bitblast_binary_app.case_0 EoCases.__bv_bitblast_binary_app.case_1 EoCases.__bv_bitblast_binary_app.case_2 EoCases.__bv_bitblast_binary_app.case_3
  logos_eq

theorem body_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_binary_app x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fbinary_5fapp.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  case_step with case_3_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 hc3 in EoCases.__bv_bitblast_binary_app.case_0 EoCases.__bv_bitblast_binary_app.case_1 EoCases.__bv_bitblast_binary_app.case_2 EoCases.__bv_bitblast_binary_app.case_3

theorem eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fbinary_5fapp.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fbinary_5fapp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fbinary_5fapp s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_binary_app x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fbinary_5fapp_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fhead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fhead s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_head.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_head.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fhead
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_head.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_head.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_head.case_0
  case_done hinv1 hG with h_v5 in EoCases.__bv_bitblast_head.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_head` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fhead.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_bitblast_head x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_head.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_head
  unfold EoCases.__bv_bitblast_head.case_0
  logos_eq

theorem body_eo__24bv_5fbitblast_5fhead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fbitblast_5fhead s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_head x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fhead.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fbitblast_5fhead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fhead_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_bitblast_head.case_0

theorem eo__24bv_5fbitblast_5fhead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fhead.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fbitblast_5fhead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fhead s1 a0) (fun s' t => Represents.rep s' t (__bv_bitblast_head x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fhead_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5ftail_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5ftail s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_tail.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_tail.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5ftail
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_tail.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_tail.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_tail.case_0
  case_done hinv1 hG with h_v2 in EoCases.__bv_bitblast_tail.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_tail` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5ftail.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_bitblast_tail x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_tail.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_tail
  unfold EoCases.__bv_bitblast_tail.case_0
  logos_eq

theorem body_eo__24bv_5fbitblast_5ftail_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fbitblast_5ftail s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_tail x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5ftail.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fbitblast_5ftail
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5ftail_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_bitblast_tail.case_0

theorem eo__24bv_5fbitblast_5ftail_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5ftail.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fbitblast_5ftail
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5ftail s1 a0) (fun s' t => Represents.rep s' t (__bv_bitblast_tail x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5ftail_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitwidth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitwidth s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitwidth.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitwidth.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitwidth
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitwidth.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_bitwidth.case_0
  case_done hinv1 hG with h_v2 in EoCases.__bv_bitwidth.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__bv_bitwidth` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitwidth.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_bitwidth x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitwidth.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitwidth
  unfold EoCases.__bv_bitwidth.case_0
  logos_eq

theorem body_eo__24bv_5fbitwidth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fbitwidth s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitwidth x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitwidth.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fbitwidth
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fbitwidth_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_bitwidth.case_0

theorem eo__24bv_5fbitwidth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitwidth.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fbitwidth
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitwidth s1 a0) (fun s' t => Represents.rep s' t (__bv_bitwidth x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitwidth_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
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

/-- logos's `__eo_is_list_nil__at__at_TypedList_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil__at__at_TypedList_cons x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil__at__at_TypedList_cons
  unfold EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0
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
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil__at__at_TypedList_cons.case_0

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
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_is_list_nil_str_concat.case_0 using hn_a0

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

theorem case_0_eo__24eo_5flit_5ftype_5fBinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fBinary s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_Binary.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_Binary.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fBinary
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_len s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_mk_rep s2 v0 v1 _ _ hinv2 h64 h_v0 h_v1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_lit_type_Binary.case_0 using hn_a0

/-- logos's `__eo_lit_type_Binary` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fBinary.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_Binary x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_Binary.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_Binary
  unfold EoCases.__eo_lit_type_Binary.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fBinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fBinary s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Binary x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fBinary.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fBinary
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fBinary_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_Binary.case_0

theorem eo__24eo_5flit_5ftype_5fBinary_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fBinary.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fBinary
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fBinary s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_Binary x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fBinary_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fNumeral_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fNumeral s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_Numeral.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_Numeral.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fNumeral
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_lit_type_Numeral.case_0 using hn_a0

/-- logos's `__eo_lit_type_Numeral` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fNumeral.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_Numeral x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_Numeral.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_Numeral
  unfold EoCases.__eo_lit_type_Numeral.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fNumeral_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fNumeral s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Numeral x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fNumeral.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fNumeral
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fNumeral_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_Numeral.case_0

theorem eo__24eo_5flit_5ftype_5fNumeral_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fNumeral.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fNumeral
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fNumeral s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_Numeral x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fNumeral_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fRational_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fRational s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_Rational.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_Rational.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fRational
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_lit_type_Rational.case_0 using hn_a0

/-- logos's `__eo_lit_type_Rational` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fRational.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_Rational x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_Rational.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_Rational
  unfold EoCases.__eo_lit_type_Rational.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fRational_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fRational s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_Rational x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fRational.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fRational
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fRational_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_Rational.case_0

theorem eo__24eo_5flit_5ftype_5fRational_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fRational.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fRational
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fRational s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_Rational x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fRational_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5flit_5ftype_5fString_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5flit_5ftype_5fString s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_lit_type_String.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_lit_type_String.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5flit_5ftype_5fString
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Seq.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with Store.apply_rep s2 v0 v1 _ _ hinv2 h64 h_v0 h_v1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_lit_type_String.case_0 using hn_a0

/-- logos's `__eo_lit_type_String` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5flit_5ftype_5fString.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_lit_type_String x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_lit_type_String.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_lit_type_String
  unfold EoCases.__eo_lit_type_String.case_0
  logos_eq

theorem body_eo__24eo_5flit_5ftype_5fString_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5flit_5ftype_5fString s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_lit_type_String x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5flit_5ftype_5fString.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5flit_5ftype_5fString
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5flit_5ftype_5fString_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_lit_type_String.case_0

theorem eo__24eo_5flit_5ftype_5fString_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5flit_5ftype_5fString.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5flit_5ftype_5fString
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5flit_5ftype_5fString s1 a0) (fun s' t => Represents.rep s' t (__eo_lit_type_String x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5flit_5ftype_5fString_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_nil__at__at_TypedList_cons.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_nil__at__at_TypedList_cons.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fnil_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_nil__at__at_TypedList_cons.case_0 using hn_a0

/-- logos's `__eo_nil__at__at_TypedList_cons` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fnil_5f_40_40TypedList_2econs.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_nil__at__at_TypedList_cons x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_nil__at__at_TypedList_cons.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_nil__at__at_TypedList_cons
  unfold EoCases.__eo_nil__at__at_TypedList_cons.case_0
  logos_eq

theorem body_eo__24eo_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fnil_5f_40_40TypedList_2econs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil__at__at_TypedList_cons x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fnil_5f_40_40TypedList_2econs.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fnil_5f_40_40TypedList_2econs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fnil_5f_40_40TypedList_2econs_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_nil__at__at_TypedList_cons.case_0

theorem eo__24eo_5fnil_5f_40_40TypedList_2econs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fnil_5f_40_40TypedList_2econs.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fnil_5f_40_40TypedList_2econs
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fnil_5f_40_40TypedList_2econs s1 a0) (fun s' t => Represents.rep s' t (__eo_nil__at__at_TypedList_cons x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fnil_5f_40_40TypedList_2econs_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_nil_str_concat.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_nil_str_concat.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fnil_5fstr_2e_2b_2b
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_nil_str_concat.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_nil_str_concat.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Seq.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  store_step with ih.eo__24seq_5fempty s3 v5 _ hinv3 h64 (hG.rem hrem) h_v5 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_nil_str_concat.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_nil_str_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fnil_5fstr_2e_2b_2b.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_nil_str_concat x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_nil_str_concat.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_nil_str_concat
  unfold EoCases.__eo_nil_str_concat.case_0
  logos_eq

theorem body_eo__24eo_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fnil_5fstr_2e_2b_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_nil_str_concat x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fnil_5fstr_2e_2b_2b.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fnil_5fstr_2e_2b_2b
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fnil_5fstr_2e_2b_2b_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_nil_str_concat.case_0

theorem eo__24eo_5fnil_5fstr_2e_2b_2b_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fnil_5fstr_2e_2b_2b.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fnil_5fstr_2e_2b_2b
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fnil_5fstr_2e_2b_2b s1 a0) (fun s' t => Represents.rep s' t (__eo_nil_str_concat x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fnil_5fstr_2e_2b_2b_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fand_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fand_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_and_intro.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_and_intro.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fand_5fintro
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_and_intro.case_0
  case_done hinv hG with h_v1 in EoCases.__eo_prog_and_intro.case_0 using

/-- logos's `__eo_prog_and_intro` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fand_5fintro.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_and_intro x_a0 =
      (firstSome [EoCases.__eo_prog_and_intro.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_and_intro
  unfold EoCases.__eo_prog_and_intro.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fand_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fand_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_and_intro x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fand_5fintro.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fand_5fintro
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fand_5fintro_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_and_intro.case_0

theorem eo__24eo_5fprog_5fand_5fintro_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fand_5fintro.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fand_5fintro
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fand_5fintro s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_and_intro x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fand_5fintro_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2dabs_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2dabs_2deq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_abs_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_abs_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2dabs_2deq more_0_eo__24eo_5fprog_5farith_2dabs_2deq more_1_eo__24eo_5fprog_5farith_2dabs_2deq
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_abs.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_abs.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v4 v6 _ _ hinv7 h64 h_v4 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v9 v12 _ _ hinv13 h64 h_v9 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v15 a0 _ _ hinv16 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v17 a1 _ _ hinv18 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v16 v18 _ _ hinv19 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v14 v19 _ _ hinv20 h64 h_v14 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.literal_boolean_spec s21 false hinv21 h64 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v20 v21 _ _ hinv22 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v13 v22 _ _ hinv23 h64 h_v13 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s24 v8 v23 _ _ hinv24 h64 h_v8 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  case_done hinv25 hG with h_v24 in EoCases.__eo_prog_arith_abs_eq.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_abs_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2dabs_2deq.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_abs_eq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_abs_eq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_abs_eq
  unfold EoCases.__eo_prog_arith_abs_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2dabs_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2dabs_2deq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_abs_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2dabs_2deq.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2dabs_2deq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2dabs_2deq_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_abs_eq.case_0

theorem eo__24eo_5fprog_5farith_2dabs_2deq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2dabs_2deq.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2dabs_2deq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2dabs_2deq s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_abs_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2dabs_2deq_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_abs_int_gt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_abs_int_gt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt more_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt more_1_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt more_2_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt more_3_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_abs.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_abs.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v4 v6 _ _ hinv7 h64 h_v4 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3e_3d.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3e_3d.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v16 a1 _ _ hinv17 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v17 v18 _ _ hinv19 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s20 v15 v19 _ _ hinv20 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3e.construct s21 e_v21 (by rw [he_v21]; exact empty_args) hinv21 h64 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v21 a0 _ _ hinv22 h64 h_v21 h_a0 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v22 a1 _ _ hinv23 h64 h_v22 h_a1 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s24 v20 v23 _ _ hinv24 h64 h_v20 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3e.construct s25 e_v25 (by rw [he_v25]; exact empty_args) hinv25 h64 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s26 v25 a0 _ _ hinv26 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s27 e_v27 (by rw [he_v27]; exact empty_args) hinv27 h64 as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s28 v27 a1 _ _ hinv28 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s29 v26 v28 _ _ hinv29 h64 h_v26 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s30, hinv30, h_v29⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s30 v24 v29 _ _ hinv30 h64 h_v24 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s31, hinv31, h_v30⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s31 v14 v30 _ _ hinv31 h64 h_v14 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s32, hinv32, h_v31⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_ite.construct s32 e_v32 (by rw [he_v32]; exact empty_args) hinv32 h64 as ⟨v32, s33, hinv33, h_v32⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s33 e_v33 (by rw [he_v33]; exact empty_args) hinv33 h64 as ⟨v33, s34, hinv34, h_v33⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s34 v33 a1 _ _ hinv34 h64 h_v33 h_a1 (by ns_tac) (by ns_tac) as ⟨v34, s35, hinv35, h_v34⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v35, s36, hinv36, h_v35⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s36 v34 v35 _ _ hinv36 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s37, hinv37, h_v36⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s37 v32 v36 _ _ hinv37 h64 h_v32 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s38, hinv38, h_v37⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3e.construct s38 e_v38 (by rw [he_v38]; exact empty_args) hinv38 h64 as ⟨v38, s39, hinv39, h_v38⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s39 e_v39 (by rw [he_v39]; exact empty_args) hinv39 h64 as ⟨v39, s40, hinv40, h_v39⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s40 v39 a0 _ _ hinv40 h64 h_v39 h_a0 (by ns_tac) (by ns_tac) as ⟨v40, s41, hinv41, h_v40⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s41 v38 v40 _ _ hinv41 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s42, hinv42, h_v41⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s42 v41 a1 _ _ hinv42 h64 h_v41 h_a1 (by ns_tac) (by ns_tac) as ⟨v42, s43, hinv43, h_v42⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s43 v37 v42 _ _ hinv43 h64 h_v37 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s44, hinv44, h_v43⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3e.construct s44 e_v44 (by rw [he_v44]; exact empty_args) hinv44 h64 as ⟨v44, s45, hinv45, h_v44⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s45 e_v45 (by rw [he_v45]; exact empty_args) hinv45 h64 as ⟨v45, s46, hinv46, h_v45⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s46 v45 a0 _ _ hinv46 h64 h_v45 h_a0 (by ns_tac) (by ns_tac) as ⟨v46, s47, hinv47, h_v46⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s47 v44 v46 _ _ hinv47 h64 h_v44 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s48, hinv48, h_v47⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s48 e_v48 (by rw [he_v48]; exact empty_args) hinv48 h64 as ⟨v48, s49, hinv49, h_v48⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s49 v48 a1 _ _ hinv49 h64 h_v48 h_a1 (by ns_tac) (by ns_tac) as ⟨v49, s50, hinv50, h_v49⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s50 v47 v49 _ _ hinv50 h64 h_v47 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s51, hinv51, h_v50⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s51 v43 v50 _ _ hinv51 h64 h_v43 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s52, hinv52, h_v51⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s52 v31 v51 _ _ hinv52 h64 h_v31 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s53, hinv53, h_v52⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s53 v8 v52 _ _ hinv53 h64 h_v8 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s54, hinv54, h_v53⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  case_done hinv54 hG with h_v53 in EoCases.__eo_prog_arith_abs_int_gt.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_abs_int_gt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2dabs_2dint_2dgt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_abs_int_gt x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_abs_int_gt.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_abs_int_gt
  unfold EoCases.__eo_prog_arith_abs_int_gt.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_abs_int_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2dabs_2dint_2dgt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_abs_int_gt.case_0

theorem eo__24eo_5fprog_5farith_2dabs_2dint_2dgt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2dabs_2dint_2dgt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2dabs_2dint_2dgt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_abs_int_gt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_div_int_to_real.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_div_int_to_real.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal more_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__2f.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__2f.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_to_5freal.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_to_5freal.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_arith_div_int_to_real.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_div_int_to_real` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_div_int_to_real x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_div_int_to_real.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_div_int_to_real
  unfold EoCases.__eo_prog_arith_div_int_to_real.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_div_int_to_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_div_int_to_real.case_0

theorem eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_div_int_to_real x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_div_total_int_to_real.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_div_total_int_to_real.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal more_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_to_5freal.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_to_5freal.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_arith_div_total_int_to_real.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_div_total_int_to_real` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_div_total_int_to_real x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_div_total_int_to_real.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_div_total_int_to_real
  unfold EoCases.__eo_prog_arith_div_total_int_to_real.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_div_total_int_to_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_div_total_int_to_real.case_0

theorem eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_div_total_int_to_real x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2ddivisible_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2ddivisible_2delim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_divisible_elim.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_divisible_elim.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2ddivisible_2delim more_0_eo__24eo_5fprog_5farith_2ddivisible_2delim more_1_eo__24eo_5fprog_5farith_2ddivisible_2delim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_arith_divisible_elim.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_divisible.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s6 v19 a0 _ _ hinv6 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s8 v18 v21 _ _ hinv8 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v23 (by rw [he_v23]; exact empty_args) hinv9 h64 as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s10 e_v24 (by rw [he_v24]; exact empty_args) hinv10 h64 as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s11 v24 a1 _ _ hinv11 h64 h_v24 h_a1 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s12 v25 a0 _ _ hinv12 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s13 v23 v26 _ _ hinv13 h64 h_v23 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s15 v27 v28 _ _ hinv15 h64 h_v27 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s16 v22 v29 _ _ hinv16 h64 h_v22 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  case_done hinv17 hG with h_v30 in EoCases.__eo_prog_arith_divisible_elim.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_arith_divisible_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2ddivisible_2delim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_arith_divisible_elim x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_divisible_elim.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_divisible_elim
  unfold EoCases.__eo_prog_arith_divisible_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2ddivisible_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5farith_2ddivisible_2delim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_divisible_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2ddivisible_2delim.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5farith_2ddivisible_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2ddivisible_2delim_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_divisible_elim.case_0

theorem eo__24eo_5fprog_5farith_2ddivisible_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2ddivisible_2delim.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5farith_2ddivisible_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2ddivisible_2delim s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_arith_divisible_elim x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2ddivisible_2delim_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2delim_2dgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2delim_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_elim_gt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_elim_gt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2delim_2dgt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v4 v9 _ _ hinv10 h64 h_v4 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_arith_elim_gt.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_elim_gt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2delim_2dgt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_elim_gt x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_elim_gt.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_elim_gt
  unfold EoCases.__eo_prog_arith_elim_gt.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2delim_2dgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2delim_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2delim_2dgt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2delim_2dgt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2delim_2dgt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_elim_gt.case_0

theorem eo__24eo_5fprog_5farith_2delim_2dgt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2delim_2dgt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2delim_2dgt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2delim_2dgt s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_elim_gt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2delim_2dgt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_elim_int_gt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_elim_int_gt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt more_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__2b.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v8 v13 _ _ hinv14 h64 h_v8 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v6 v14 _ _ hinv15 h64 h_v6 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v4 v15 _ _ hinv16 h64 h_v4 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_arith_elim_int_gt.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_elim_int_gt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2delim_2dint_2dgt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_elim_int_gt x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_elim_int_gt.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_elim_int_gt
  unfold EoCases.__eo_prog_arith_elim_int_gt.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_int_gt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2delim_2dint_2dgt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_elim_int_gt.case_0

theorem eo__24eo_5fprog_5farith_2delim_2dint_2dgt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2delim_2dint_2dgt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2delim_2dint_2dgt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_elim_int_gt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_elim_int_lt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_elim_int_lt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt more_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__2b.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v11 v12 _ _ hinv13 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v8 v13 _ _ hinv14 h64 h_v8 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v6 v14 _ _ hinv15 h64 h_v6 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v4 v15 _ _ hinv16 h64 h_v4 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_arith_elim_int_lt.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_elim_int_lt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2delim_2dint_2dlt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_elim_int_lt x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_elim_int_lt.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_elim_int_lt
  unfold EoCases.__eo_prog_arith_elim_int_lt.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_int_lt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2delim_2dint_2dlt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_elim_int_lt.case_0

theorem eo__24eo_5fprog_5farith_2delim_2dint_2dlt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2delim_2dint_2dlt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2delim_2dint_2dlt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_elim_int_lt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2delim_2dleq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2delim_2dleq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_elim_leq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_elim_leq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2delim_2dleq
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_arith_elim_leq.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_elim_leq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2delim_2dleq.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_elim_leq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_elim_leq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_elim_leq
  unfold EoCases.__eo_prog_arith_elim_leq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2delim_2dleq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2delim_2dleq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_leq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2delim_2dleq.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2delim_2dleq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2delim_2dleq_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_elim_leq.case_0

theorem eo__24eo_5fprog_5farith_2delim_2dleq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2delim_2dleq.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2delim_2dleq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2delim_2dleq s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_elim_leq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2delim_2dleq_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2delim_2dlt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2delim_2dlt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_elim_lt.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_elim_lt.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2delim_2dlt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v4 v9 _ _ hinv10 h64 h_v4 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_arith_elim_lt.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_elim_lt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2delim_2dlt.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_elim_lt x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_elim_lt.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_elim_lt
  unfold EoCases.__eo_prog_arith_elim_lt.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2delim_2dlt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2delim_2dlt s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_elim_lt x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2delim_2dlt.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2delim_2dlt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2delim_2dlt_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_elim_lt.case_0

theorem eo__24eo_5fprog_5farith_2delim_2dlt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2delim_2dlt.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2delim_2dlt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2delim_2dlt s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_elim_lt x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2delim_2dlt_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_eq_elim_int.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_eq_elim_int.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint more_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_and.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_and.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3c_3d.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a1 _ _ hinv13 h64 h_v12 h_a1 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v10 v13 _ _ hinv14 h64 h_v10 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v14 v15 _ _ hinv16 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v9 v16 _ _ hinv17 h64 h_v9 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v4 v17 _ _ hinv18 h64 h_v4 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv19 hG with h_v18 in EoCases.__eo_prog_arith_eq_elim_int.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_eq_elim_int` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2deq_2delim_2dint.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_eq_elim_int x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_eq_elim_int.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_eq_elim_int
  unfold EoCases.__eo_prog_arith_eq_elim_int.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2deq_2delim_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2deq_2delim_2dint s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_eq_elim_int x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2deq_2delim_2dint.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2deq_2delim_2dint
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_eq_elim_int.case_0

theorem eo__24eo_5fprog_5farith_2deq_2delim_2dint_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2deq_2delim_2dint.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2deq_2delim_2dint
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2deq_2delim_2dint s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_eq_elim_int x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2deq_2delim_2dint_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_arith_eq_elim_real.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_arith_eq_elim_real.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal more_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_and.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3e_3d.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_and.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3c_3d.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v12 a1 _ _ hinv13 h64 h_v12 h_a1 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s14 v10 v13 _ _ hinv14 h64 h_v10 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v14 v15 _ _ hinv16 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v9 v16 _ _ hinv17 h64 h_v9 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v4 v17 _ _ hinv18 h64 h_v4 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv19 hG with h_v18 in EoCases.__eo_prog_arith_eq_elim_real.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_arith_eq_elim_real` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5farith_2deq_2delim_2dreal.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_arith_eq_elim_real x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_arith_eq_elim_real.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_arith_eq_elim_real
  unfold EoCases.__eo_prog_arith_eq_elim_real.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_arith_eq_elim_real x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5farith_2deq_2delim_2dreal.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_arith_eq_elim_real.case_0

theorem eo__24eo_5fprog_5farith_2deq_2delim_2dreal_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5farith_2deq_2delim_2dreal.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5farith_2deq_2delim_2dreal
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_arith_eq_elim_real x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
