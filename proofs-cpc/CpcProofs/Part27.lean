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
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping h_a1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping hinv1 s1
  have h_req_v2 := (show requires_0_eo__24eo_5ftypeof_5f_2b s2 v0 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5f_2b
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    req_done hinv2 hG with h_a0 using hq_v0)
  store_step with h_req_v2 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a0 h_req_v2 h_v0 h_v1 hinv2 s2 v0 v1
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
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping h_a0 h_a1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_v0 dropping hinv1 s1
  have h_req_v3 := (show requires_0_eo__24eo_5ftypeof_5f_2f s2 v0 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5f_2f
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    step as ⟨e_v2, he_v2⟩
    store_step with CtorSpec.eo_Real.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_v0 h_v1 he_v2 hinv2 e_v2 s2 v0 v1
    req_done hinv3 hG with h_v2 using hq_v0)
  store_step with h_req_v3 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_req_v3 h_v0 h_v1 hinv2 s2 v0 v1
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
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping h_a0 h_a1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_v0 dropping hinv1 s1
  have h_req_v3 := (show requires_0_eo__24eo_5ftypeof_5f_3c s2 v0 v1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5f_3c
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    step as ⟨e_v2, he_v2⟩
    store_step with CtorSpec.eo__24emb_5fBool.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_v0 h_v1 he_v2 hinv2 e_v2 s2 v0 v1
    req_done hinv3 hG with h_v2 using hq_v0)
  store_step with h_req_v3 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_req_v3 h_v0 h_v1 hinv2 s2 v0 v1
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
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping h_a0 h_a1 he_v0 e_v0
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
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_Pair.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at__at_Pair.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
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
  store_step with CtorSpec.eo__40_40TypedList.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2 dropping h_a1 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_TypedList_cons.case_0
  pat_same v2 a0 with h_v2 h_a0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_TypedList_cons.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 dropping h_v1 h_v2 h_v3 he_v4 hinv1 e_v4 s1 v1 v2 v3
  store_step with Store.apply_rep s2 v4 a0 _ _ hinv2 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_a0 h_v4 hinv2 s2 v4
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
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_TypedList_nil.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 hinv2 s2 v1
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
  store_step with CtorSpec.eo__24eo_5fList.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_mon.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Real.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at__at_mon.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__40_40Monomial.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
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
  store_step with CtorSpec.eo__40_40Pair.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 hinv1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 hinv2 s2 v1
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
  store_step with CtorSpec.eo__40_40Monomial.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at__at_poly.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40Polynomial.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at__at_poly.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__40_40Polynomial.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
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
  store_step with CtorSpec.eo_Array.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_array_deq_diff.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_Array.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a1 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
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
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_bit.case_0
  pat_unapply h_a1 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_bit.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_a0 h_a1 h_v0 h_v3 he_v4 hinv1 e_v4 s1 v0 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_bit.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
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
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_bvsize.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
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
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_const.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
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
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_div_by_zero.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Real.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
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

theorem case_0_eo__24eo_5ftypeof_5f_40from_5fbools_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40from_5fbools s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_from_bools.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_from_bools.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40from_5fbools
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_from_bools.case_0
  pat_unapply h_a1 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_from_bools.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 h_v3 dropping h_a0 h_a1 h_v0 he_v4 hinv1 e_v4 s1 v0
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_from_bools.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_BitVec.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v3 dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v3 h_v5 dropping hinv3 s3
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_add s4 e_v7 (by rw [he_v7]; rfl) h_v6 h_v3 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v5 dropping h_v3 h_v6 he_v7 hinv4 e_v7 s4 v3 v6
  store_step with Store.apply_mk_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v5 h_v7 hinv5 s5 v5 v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_typeof__at_from_bools.case_0 using hn_a0 hn_a1 hn_v2 hn_v3

/-- logos's `__eo_typeof__at_from_bools` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40from_5fbools.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_from_bools x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_from_bools.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_from_bools
  unfold EoCases.__eo_typeof__at_from_bools.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40from_5fbools_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40from_5fbools s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_from_bools x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40from_5fbools.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40from_5fbools
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40from_5fbools_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_from_bools.case_0

theorem eo__24eo_5ftypeof_5f_40from_5fbools_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40from_5fbools.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40from_5fbools
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40from_5fbools s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_from_bools x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40from_5fbools_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40purify_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40purify s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_purify.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_purify.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40purify
  have hG := Store.Grows.refl s
  case_done hinv hG with h_a0 in EoCases.__eo_typeof__at_purify.case_0 using hn_a0

/-- logos's `__eo_typeof__at_purify` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40purify.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof__at_purify x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_purify.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_purify
  unfold EoCases.__eo_typeof__at_purify.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40purify_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5f_40purify s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_purify x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40purify.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5f_40purify
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40purify_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof__at_purify.case_0

theorem eo__24eo_5ftypeof_5f_40purify_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40purify.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5f_40purify
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40purify s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof__at_purify x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40purify_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_quantifiers_skolemize.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_quantifiers_skolemize.case_0
  store_step with ih.eo__24get_5fnth_5fvar_5ftype s2 a1 a3 _ _ hinv2 h64 (hG.rem hrem) h_a1 h_a3 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a1 h_a2 h_a3 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof__at_quantifiers_skolemize.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_typeof__at_quantifiers_skolemize` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_typeof__at_quantifiers_skolemize x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_quantifiers_skolemize.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_quantifiers_skolemize
  unfold EoCases.__eo_typeof__at_quantifiers_skolemize.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_quantifiers_skolemize x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_typeof__at_quantifiers_skolemize.case_0

theorem eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 796#u32 _ [a0, a1, a2, a3] rfl
    (fun s1 => body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_typeof__at_quantifiers_skolemize x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, y0, y1, y2, y3, hargs, hb0, hb1, hb2, hb3, hr⟩ := ProgramSem.of_796 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_796 ⟨a0, a1, a2, a3, x_a0, x_a1, x_a2, x_a3, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40quantifiers_5fskolemize_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_a2 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_RegLan.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 h_a2 dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  pat_same a1 v5 with h_a1 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Int.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a2 dropping h_a1 h_v5 he_v6 hinv3 e_v6 s3 v5
  pat_same a2 v6 with h_a2 h_v6 using hinv4 else hinv4 hG in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_Seq.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_a2 h_v6 he_v7 hinv4 e_v7 s4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_Char.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v7 dropping he_v8 hinv5 e_v8 s5
  store_step with Store.apply_rep s6 v7 v8 _ _ hinv6 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying dropping h_v7 h_v8 hinv6 s6 v7 v8
  case_done hinv7 hG with h_v9 in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__eo_typeof__at_re_unfold_pos_component` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_typeof__at_re_unfold_pos_component x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_re_unfold_pos_component.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_re_unfold_pos_component
  unfold EoCases.__eo_typeof__at_re_unfold_pos_component.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_re_unfold_pos_component x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_typeof__at_re_unfold_pos_component.case_0

theorem eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_typeof__at_re_unfold_pos_component x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40re_5funfold_5fpos_5fcomponent_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_sets_deq_diff.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_sets_deq_diff.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_sets_deq_diff.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Set.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_sets_deq_diff.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_sets_deq_diff.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_Set.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_sets_deq_diff.case_0
  pat_same v6 v2 with h_v6 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_sets_deq_diff.case_0
  case_done hinv2 hG with h_v2 in EoCases.__eo_typeof__at_sets_deq_diff.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v5 hn_v6

/-- logos's `__eo_typeof__at_sets_deq_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_sets_deq_diff x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_sets_deq_diff.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_sets_deq_diff
  unfold EoCases.__eo_typeof__at_sets_deq_diff.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_sets_deq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_sets_deq_diff.case_0

theorem eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_sets_deq_diff x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40sets_5fdeq_5fdiff_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_strings_deq_diff.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_strings_deq_diff.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_strings_deq_diff.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_deq_diff.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_deq_diff.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_Seq.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_deq_diff.case_0
  pat_same v6 v2 with h_v6 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_deq_diff.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_Int.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v2 h_v5 h_v6 h_v7 he_v8 hinv2 e_v8 s2 v2 v5 v6 v7
  case_done hinv3 hG with h_v8 in EoCases.__eo_typeof__at_strings_deq_diff.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v5 hn_v6

/-- logos's `__eo_typeof__at_strings_deq_diff` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_strings_deq_diff x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_strings_deq_diff.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_strings_deq_diff
  unfold EoCases.__eo_typeof__at_strings_deq_diff.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_deq_diff x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_strings_deq_diff.case_0

theorem eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_strings_deq_diff x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40strings_5fdeq_5fdiff_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_strings_num_occur_re.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_strings_num_occur_re.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_strings_num_occur_re.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_num_occur_re.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_num_occur_re.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_RegLan.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  pat_same a1 v5 with h_a1 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_strings_num_occur_re.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Int.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_a1 h_v5 he_v6 hinv3 e_v6 s3 v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_typeof__at_strings_num_occur_re.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

/-- logos's `__eo_typeof__at_strings_num_occur_re` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_strings_num_occur_re x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_strings_num_occur_re.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_strings_num_occur_re
  unfold EoCases.__eo_typeof__at_strings_num_occur_re.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_num_occur_re x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_strings_num_occur_re.case_0

theorem eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_strings_num_occur_re x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40strings_5fnum_5foccur_5fre_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_strings_replace_all_result.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_strings_replace_all_result.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_a2 h_a3 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_Seq.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a2 h_a3 h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  pat_same v6 v2 with h_v6 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  pat_unapply h_a2 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_Seq.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a3 h_v2 h_v9 h_v10 dropping h_a2 h_v5 h_v6 h_v7 he_v11 hinv2 e_v11 s2 v5 v6 v7
  pat_same v9 v11 with h_v9 h_v11 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  pat_same v10 v2 with h_v10 h_v2 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_Int.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a3 h_v2 dropping h_v10 h_v11 h_v9 he_v12 hinv3 e_v12 s3 v10 v11 v9
  pat_same a3 v12 with h_a3 h_v12 using hinv4 else hinv4 hG in EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_Seq.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 dropping h_a3 h_v12 he_v13 hinv4 e_v13 s4 v12
  store_step with Store.apply_rep s5 v13 v2 _ _ hinv5 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying dropping h_v13 h_v2 hinv5 s5 v13 v2
  case_done hinv6 hG with h_v14 in EoCases.__eo_typeof__at_strings_replace_all_result.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2 hn_v5 hn_v6 hn_v9 hn_v10

/-- logos's `__eo_typeof__at_strings_replace_all_result` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_typeof__at_strings_replace_all_result x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_strings_replace_all_result.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_strings_replace_all_result
  unfold EoCases.__eo_typeof__at_strings_replace_all_result.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_replace_all_result x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_typeof__at_strings_replace_all_result.case_0

theorem eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_typeof__at_strings_replace_all_result x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fall_5fresult_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_a2 h_a3 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_a2 h_a3 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_RegLan.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  pat_same a1 v5 with h_a1 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  pat_unapply h_a2 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_Seq.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a3 h_v7 h_v8 dropping h_a1 h_a2 h_v5 he_v9 hinv3 e_v9 s3 v5
  pat_same v7 v9 with h_v7 h_v9 using hinv4 else hinv4 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_Char.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a3 h_v8 dropping h_v7 h_v9 he_v10 hinv4 e_v10 s4 v7 v9
  pat_same v8 v10 with h_v8 h_v10 using hinv5 else hinv5 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_Int.construct s5 e_v11 (by rw [he_v11]; exact empty_args) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a3 dropping h_v10 h_v8 he_v11 hinv5 e_v11 s5 v10 v8
  pat_same a3 v11 with h_a3 h_v11 using hinv6 else hinv6 hG in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_Seq.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying dropping h_a3 h_v11 he_v12 hinv6 e_v12 s6 v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_Char.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v12 v13 _ _ hinv8 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying dropping h_v12 h_v13 hinv8 s8 v12 v13
  case_done hinv9 hG with h_v14 in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2 hn_v7 hn_v8

/-- logos's `__eo_typeof__at_strings_replace_re_all_result` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_typeof__at_strings_replace_re_all_result x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_strings_replace_re_all_result
  unfold EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_replace_re_all_result x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_typeof__at_strings_replace_re_all_result.case_0

theorem eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_typeof__at_strings_replace_re_all_result x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40strings_5freplace_5fre_5fall_5fresult_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_strings_stoi_result.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_strings_stoi_result.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof__at_strings_stoi_result.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_strings_stoi_result.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_strings_stoi_result.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_Int.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  pat_same a1 v5 with h_a1 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_strings_stoi_result.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_Int.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_a1 h_v5 he_v6 hinv3 e_v6 s3 v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_typeof__at_strings_stoi_result.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

/-- logos's `__eo_typeof__at_strings_stoi_result` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof__at_strings_stoi_result x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_strings_stoi_result.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_strings_stoi_result
  unfold EoCases.__eo_typeof__at_strings_stoi_result.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_strings_stoi_result x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof__at_strings_stoi_result.case_0

theorem eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof__at_strings_stoi_result x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40strings_5fstoi_5fresult_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof__at_witness_string_length.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof__at_witness_string_length.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof__at_witness_string_length.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_typeof__at_witness_string_length.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_Int.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a1 h_a3 dropping h_a2 h_v1 he_v2 hinv2 e_v2 s2 v1
  pat_same a3 v2 with h_a3 h_v2 using hinv3 else hinv3 hG in EoCases.__eo_typeof__at_witness_string_length.case_0
  case_done hinv3 hG with h_a1 in EoCases.__eo_typeof__at_witness_string_length.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_typeof__at_witness_string_length` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5f_40witness_5fstring_5flength.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_typeof__at_witness_string_length x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof__at_witness_string_length.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof__at_witness_string_length
  unfold EoCases.__eo_typeof__at_witness_string_length.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof__at_witness_string_length x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5f_40witness_5fstring_5flength.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_typeof__at_witness_string_length.case_0

theorem eo__24eo_5ftypeof_5f_40witness_5fstring_5flength_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5f_40witness_5fstring_5flength.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5ftypeof_5f_40witness_5fstring_5flength
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_typeof__at_witness_string_length x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5f_40witness_5fstring_5flength_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fBitVec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fBitVec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_BitVec.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_BitVec.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fBitVec
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_BitVec.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof_BitVec.case_0 using hn_a0

/-- logos's `__eo_typeof_BitVec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fBitVec.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_BitVec x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_BitVec.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_BitVec
  unfold EoCases.__eo_typeof_BitVec.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fBitVec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fBitVec s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_BitVec x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fBitVec.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fBitVec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fBitVec_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_BitVec.case_0

theorem eo__24eo_5ftypeof_5fBitVec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fBitVec.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fBitVec
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fBitVec s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_BitVec x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fBitVec_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fSeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fSeq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_Seq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_Seq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fSeq
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_typeof_Seq.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fType.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_typeof_Seq.case_0 using hn_a0

/-- logos's `__eo_typeof_Seq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fSeq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_Seq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_Seq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_Seq
  unfold EoCases.__eo_typeof_Seq.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fSeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fSeq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_Seq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fSeq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fSeq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fSeq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_Seq.case_0

theorem eo__24eo_5ftypeof_5fSeq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fSeq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fSeq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fSeq s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_Seq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fSeq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fabs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fabs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_abs.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_abs.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fabs
  have hG := Store.Grows.refl s
  store_step with ih.eo__24is_5farith_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping hinv1 s1
  have h_req_v2 := (show requires_0_eo__24eo_5ftypeof_5fabs s2 v0 v1 a0 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5fabs
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v0 v1 with h_v0 h_v1 using hinv2 hG
    req_stuck h_v0 as hq_v0 using hinv2 hG
    req_done hinv2 hG with h_a0 using hq_v0)
  store_step with h_req_v2 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a0 h_req_v2 h_v0 h_v1 hinv2 s2 v0 v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_typeof_abs.case_0 using hn_a0

/-- logos's `__eo_typeof_abs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fabs.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_abs x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_abs.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_abs
  unfold EoCases.__eo_typeof_abs.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fabs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fabs s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_abs x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fabs.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fabs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fabs_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_abs.case_0

theorem eo__24eo_5ftypeof_5fabs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fabs.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fabs
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fabs s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_abs x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fabs_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_apply.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_apply.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_apply.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_typeof_apply.case_0
  pat_is_node h_v4 : x_v4 is Eo.Term.FunType by Embed.inv_Term_FunType else hinv hG in EoCases.__eo_typeof_apply.case_0
  have h_req_v7 := (show requires_0_eo__24eo_5ftypeof_5fapply s v5 a1 v2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5ftypeof_5fapply
    have hG := Store.Grows.refl s
    req_same v5 a1 with h_v5 h_a1 using hinv hG
    req_stuck h_v5 as hq_v5 using hinv hG
    req_done hinv hG with h_v2 using hq_v5)
  store_step with h_req_v7 as ⟨v7, s1, hinv1, h_v7⟩ growing hG carrying dropping h_a0 h_req_v7 h_v1 h_v2 h_v4 h_v5 v1 v2 v4 v5
  case_done hinv1 hG with h_v7 in EoCases.__eo_typeof_apply.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_apply.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_apply.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fDtcAppType.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_typeof_apply.case_1
  have h_req_v3 := (show requires_1_eo__24eo_5ftypeof_5fapply s v1 a1 v2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5ftypeof_5fapply
    have hG := Store.Grows.refl s
    req_same v1 a1 with h_v1 h_a1 using hinv hG
    req_stuck h_v1 as hq_v1 using hinv hG
    req_done hinv hG with h_v2 using hq_v1)
  store_step with h_req_v3 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying dropping h_a0 h_req_v3 h_v1 h_v2 v1 v2
  case_done hinv1 hG with h_v3 in EoCases.__eo_typeof_apply.case_1 using hn_a0 hn_a1

/-- logos's `__eo_typeof_apply` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fapply.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_apply x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_apply.case_0 x_a0 x_a1, EoCases.__eo_typeof_apply.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_apply
  unfold EoCases.__eo_typeof_apply.case_0 EoCases.__eo_typeof_apply.case_1
  logos_eq

theorem body_eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fapply s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_apply x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fapply.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fapply
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fapply_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24eo_5ftypeof_5fapply_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__eo_typeof_apply.case_0 EoCases.__eo_typeof_apply.case_1

theorem eo__24eo_5ftypeof_5fapply_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fapply.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fapply
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fapply s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_apply x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fapply_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvand.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvand.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvand
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvand.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvand.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvand.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvand.case_0
  pat_same v6 v2 with h_v6 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvand.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_BitVec.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 dropping h_v5 h_v6 h_v7 he_v8 hinv2 e_v8 s2 v5 v6 v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying dropping h_v2 h_v8 hinv3 s3 v2 v8
  case_done hinv4 hG with h_v9 in EoCases.__eo_typeof_bvand.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v5 hn_v6

/-- logos's `__eo_typeof_bvand` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvand.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_bvand x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvand.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvand
  unfold EoCases.__eo_typeof_bvand.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fbvand s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvand x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvand.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fbvand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvand_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_bvand.case_0

theorem eo__24eo_5ftypeof_5fbvand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvand.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fbvand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvand s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_bvand x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvand_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvcomp.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvcomp.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvcomp
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvcomp.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvcomp.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvcomp.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvcomp.case_0
  pat_same v6 v2 with h_v6 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvcomp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_BitVec.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v2 h_v5 h_v6 h_v7 he_v8 hinv2 e_v8 s2 v2 v5 v6 v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v8 dropping hinv3 s3
  store_step with Store.apply_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v8 h_v9 hinv4 s4 v8 v9
  case_done hinv5 hG with h_v10 in EoCases.__eo_typeof_bvcomp.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v5 hn_v6

/-- logos's `__eo_typeof_bvcomp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvcomp.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_bvcomp x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvcomp.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvcomp
  unfold EoCases.__eo_typeof_bvcomp.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fbvcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvcomp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvcomp.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fbvcomp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvcomp_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_bvcomp.case_0

theorem eo__24eo_5ftypeof_5fbvcomp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvcomp.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fbvcomp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvcomp s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_bvcomp x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvcomp_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvite.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvite.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvite
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvite.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_a2 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvite.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvite.case_0
  pat_same a2 a1 with h_a2 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvite.case_0
  case_done hinv2 hG with h_a1 in EoCases.__eo_typeof_bvite.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__eo_typeof_bvite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvite.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_typeof_bvite x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvite.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvite
  unfold EoCases.__eo_typeof_bvite.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5ftypeof_5fbvite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvite.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5ftypeof_5fbvite
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvite_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_typeof_bvite.case_0

theorem eo__24eo_5ftypeof_5fbvite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvite.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5ftypeof_5fbvite
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvite s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_typeof_bvite x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvite_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvnego_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvnego s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvnego.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvnego.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvnego
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvnego.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvnego.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_typeof_bvnego.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_typeof_bvnego` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvnego.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_bvnego x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvnego.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvnego
  unfold EoCases.__eo_typeof_bvnego.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvnego_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fbvnego s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvnego x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvnego.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fbvnego
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvnego_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_bvnego.case_0

theorem eo__24eo_5ftypeof_5fbvnego_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvnego.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fbvnego
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvnego s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_bvnego x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvnego_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvnot_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvnot.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvnot.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvnot
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvnot.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvnot.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v2 h_v4 hinv2 s2 v2 v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_typeof_bvnot.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_typeof_bvnot` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvnot.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_bvnot x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvnot.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvnot
  unfold EoCases.__eo_typeof_bvnot.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvnot_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fbvnot s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvnot x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvnot.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fbvnot
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvnot_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_bvnot.case_0

theorem eo__24eo_5ftypeof_5fbvnot_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvnot.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fbvnot
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvnot s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_bvnot x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvnot_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvredand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvredand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvredand.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvredand.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvredand
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvredand.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvredand.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping hinv2 s2
  store_step with Store.apply_rep s3 v4 v5 _ _ hinv3 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv3 s3 v4 v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_typeof_bvredand.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_typeof_bvredand` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvredand.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_bvredand x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvredand.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvredand
  unfold EoCases.__eo_typeof_bvredand.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvredand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fbvredand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvredand x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvredand.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fbvredand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvredand_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_bvredand.case_0

theorem eo__24eo_5ftypeof_5fbvredand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvredand.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fbvredand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvredand s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_bvredand x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvredand_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fbvult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fbvult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_bvult.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_bvult.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fbvult
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_bvult.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvult.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof_bvult.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvult.case_0
  pat_same v6 v2 with h_v6 h_v2 using hinv2 else hinv2 hG in EoCases.__eo_typeof_bvult.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_v2 h_v5 h_v6 h_v7 he_v8 hinv2 e_v8 s2 v2 v5 v6 v7
  case_done hinv3 hG with h_v8 in EoCases.__eo_typeof_bvult.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v5 hn_v6

/-- logos's `__eo_typeof_bvult` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fbvult.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_bvult x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_bvult.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_bvult
  unfold EoCases.__eo_typeof_bvult.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fbvult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fbvult s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_bvult x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fbvult.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fbvult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fbvult_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_bvult.case_0

theorem eo__24eo_5ftypeof_5fbvult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fbvult.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fbvult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fbvult s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_bvult x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fbvult_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_concat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_concat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fconcat
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_concat.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_concat.case_0
  pat_unapply h_a1 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__eo_typeof_concat.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_BitVec.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 h_v6 dropping h_a1 h_v1 h_v3 he_v7 hinv1 e_v7 s1 v1 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__eo_typeof_concat.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_BitVec.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v6 dropping h_v5 h_v7 he_v8 hinv2 e_v8 s2 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_add s3 e_v9 (by rw [he_v9]; rfl) h_v2 h_v6 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v8 dropping h_v2 h_v6 he_v9 hinv3 e_v9 s3 v2 v6
  store_step with Store.apply_mk_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v8 h_v9 hinv4 s4 v8 v9
  case_done hinv5 hG with h_v10 in EoCases.__eo_typeof_concat.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v5 hn_v6

/-- logos's `__eo_typeof_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fconcat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_typeof_concat x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_concat.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_concat
  unfold EoCases.__eo_typeof_concat.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fconcat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5ftypeof_5fconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fconcat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_typeof_concat.case_0

theorem eo__24eo_5ftypeof_5fconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fconcat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5ftypeof_5fconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fconcat s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_typeof_concat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fconcat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5ftypeof_5fdistinct_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5ftypeof_5fdistinct s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_typeof_distinct.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_typeof_distinct.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5ftypeof_5fdistinct
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_typeof_distinct.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 dropping h_a0 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_typeof_distinct.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_typeof_distinct.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_typeof_distinct` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5ftypeof_5fdistinct.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_typeof_distinct x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_typeof_distinct.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_typeof_distinct
  unfold EoCases.__eo_typeof_distinct.case_0
  logos_eq

theorem body_eo__24eo_5ftypeof_5fdistinct_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5ftypeof_5fdistinct s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_typeof_distinct x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5ftypeof_5fdistinct.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5ftypeof_5fdistinct
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5ftypeof_5fdistinct_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_typeof_distinct.case_0

theorem eo__24eo_5ftypeof_5fdistinct_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5ftypeof_5fdistinct.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5ftypeof_5fdistinct
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5ftypeof_5fdistinct s1 a0) (fun s' t => Represents.rep s' t (__eo_typeof_distinct x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5ftypeof_5fdistinct_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
