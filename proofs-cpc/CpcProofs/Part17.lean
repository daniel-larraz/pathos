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
  rw [← Bridge.native_and] at h_v7
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
  rw [← Bridge.native_and] at h_v5
  store_step with ih.eo__24smtx_5fdt_5fcons_5fwf_5frec s3 a0 v2 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_and s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  rw [← Bridge.native_and] at h_v7
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
  rw [← Bridge.native_or] at h_v5
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
  rw [← Bridge.native_and] at h_v5
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
  rw [← Bridge.native_and] at h_v5
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
  rw [← Bridge.native_and] at h_v2
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
  rw [← Bridge.native_and] at h_v5
  store_step with ih.eo__24smtx_5finhabited_5ftype s3 v2 _ hinv3 h64 (hG.rem hrem) h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with ih.eo__24smtx_5ftype_5fwf_5frec s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.native_spec_and s5 e_v8 (by rw [he_v8]; rfl) h_v6 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  rw [← Bridge.native_and] at h_v8
  step as ⟨e_v9, he_v9⟩
  store_step with Store.native_spec_and s6 e_v9 (by rw [he_v9]; rfl) h_v5 h_v8 hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  rw [← Bridge.native_and] at h_v9
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
  rw [← Bridge.native_and] at h_v4
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
  rw [← Bridge.native_and] at h_v4
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
  rw [← Bridge.native_and] at h_v5
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

theorem case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_2.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_2.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_bv_op_2.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_bv_op_2.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_nateq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  rw [← Bridge.native_nateq] at h_v4
  have h_ite_v7 := (show if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2 s1 v4 v1 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s1 e_v5 (by rw [he_v5]; rfl) h_v1 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_true_rep _ hx_5 h_v5)
    · ite_branch hbv_5
      step as ⟨e_v6, he_v6⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v6))
  store_step with h_ite_v7 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  case_done hinv2 hG with h_v7 in EoCases.__smtx_typeof_bv_op_2.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_2.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_2.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_bv_op_2.case_1 using

/-- logos's `__smtx_typeof_bv_op_2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fbv_5fop_5f2.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_bv_op_2 x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_bv_op_2.case_0 x_a0 x_a1, EoCases.__smtx_typeof_bv_op_2.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_bv_op_2
  unfold EoCases.__smtx_typeof_bv_op_2.case_0 EoCases.__smtx_typeof_bv_op_2.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fbv_5fop_5f2 s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_2 x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fbv_5fop_5f2.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fbv_5fop_5f2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_bv_op_2.case_0 EoCases.__smtx_typeof_bv_op_2.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fbv_5fop_5f2.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fbv_5fop_5f2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fbv_5fop_5f2 s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_bv_op_2 x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_2_ret.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_2_ret.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_bv_op_2_ret.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_bv_op_2_ret.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_nateq s e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3
  rw [← Bridge.native_nateq] at h_v4
  have h_ite_v6 := (show if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s1 v4 a2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret
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
  case_done hinv2 hG with h_v6 in EoCases.__smtx_typeof_bv_op_2_ret.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_bv_op_2_ret.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_bv_op_2_ret.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_bv_op_2_ret.case_1 using

/-- logos's `__smtx_typeof_bv_op_2_ret` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_bv_op_2_ret x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_bv_op_2_ret.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_bv_op_2_ret.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_bv_op_2_ret
  unfold EoCases.__smtx_typeof_bv_op_2_ret.case_0 EoCases.__smtx_typeof_bv_op_2_ret.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_bv_op_2_ret x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_bv_op_2_ret.case_0 EoCases.__smtx_typeof_bv_op_2_ret.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_bv_op_2_ret x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fbv_5fop_5f2_5fret_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24smtx_5ftypeof_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24smtx_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_concat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_concat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fconcat
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_concat.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_concat.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_nat_to_int s e_v4 (by rw [he_v4]; rfl) h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3
  rw [← Bridge.native_nat_to_int] at h_v4
  step as ⟨e_v5, he_v5⟩
  store_step with Store.native_spec_nat_to_int s1 e_v5 (by rw [he_v5]; rfl) h_v3 hinv1 h64 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4
  rw [← Bridge.native_nat_to_int] at h_v5
  step as ⟨e_v6, he_v6⟩
  store_step with Store.native_spec_zplus s2 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv2 h64 as ⟨v6, s3, hinv3, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5
  rw [← Bridge.native_zplus] at h_v6
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_int_to_nat s3 e_v7 (by rw [he_v7]; rfl) h_v6 hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6
  rw [← Bridge.native_int_to_nat] at h_v7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s4 e_v8 (by rw [he_v8]; rfl) h_v7 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv5 hG with h_v8 in EoCases.__smtx_typeof_concat.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24smtx_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_concat.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_concat.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fconcat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_concat.case_1 using

/-- logos's `__smtx_typeof_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fconcat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __smtx_typeof_concat x_a0 x_a1 =
      (firstSome [EoCases.__smtx_typeof_concat.case_0 x_a0 x_a1, EoCases.__smtx_typeof_concat.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __smtx_typeof_concat
  unfold EoCases.__smtx_typeof_concat.case_0 EoCases.__smtx_typeof_concat.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24smtx_5ftypeof_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fconcat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24smtx_5ftypeof_5fconcat
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fconcat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24smtx_5ftypeof_5fconcat_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_concat.case_0 EoCases.__smtx_typeof_concat.case_1 splitting x_a0 x_a1

theorem eo__24smtx_5ftypeof_5fconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fconcat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24smtx_5ftypeof_5fconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fconcat s1 a0 a1) (fun s' t => Represents.rep s' t (__smtx_typeof_concat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fconcat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

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

theorem case_0_eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_0_eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_extract.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_extract.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24smtx_5ftypeof_5fextract
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__smtx_typeof_extract.case_0
  pat_destruct CtorSpec.eo__24emb_5fsm_2eNumeral.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__smtx_typeof_extract.case_0
  pat_destruct CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct h_a2 as ⟨v5, x_v5, h_v5⟩ else hinv hG in EoCases.__smtx_typeof_extract.case_0
  simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.raw_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.native_spec_zleq s1 e_v7 (by rw [he_v7]; rfl) h_v6 h_v3 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6
  rw [← Bridge.native_zleq] at h_v7
  have h_ite_v27 := (show if_2_eo__24smtx_5ftypeof_5fextract s2 v7 v5 v1 v3 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_2_eo__24smtx_5ftypeof_5fextract
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_native h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_nat_to_int s2 e_v8 (by rw [he_v8]; rfl) h_v5 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
      rw [← Bridge.native_nat_to_int] at h_v8
      step as ⟨e_v9, he_v9⟩
      store_step with Store.native_spec_zlt s3 e_v9 (by rw [he_v9]; rfl) h_v1 h_v8 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8
      rw [← Bridge.native_zlt] at h_v9
      have h_ite_v25 := (show if_1_eo__24smtx_5ftypeof_5fextract s4 v9 v1 v3 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24smtx_5ftypeof_5fextract
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_native h_v9 with ⟨hx_10, hbv_10⟩ | ⟨hx_10, hbv_10⟩
        · ite_branch hbv_10
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.raw_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.raw_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
          step as ⟨e_v12, he_v12⟩
          store_step with Store.native_spec_zplus s6 e_v12 (by rw [he_v12]; rfl) h_v1 h_v11 hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
          rw [← Bridge.native_zplus] at h_v12
          step as ⟨e_v13, he_v13⟩
          store_step with Store.native_spec_zneg s7 e_v13 (by rw [he_v13]; rfl) h_v3 hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
          rw [← Bridge.native_zneg] at h_v13
          step as ⟨e_v14, he_v14⟩
          store_step with Store.native_spec_zplus s8 e_v14 (by rw [he_v14]; rfl) h_v12 h_v13 hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
          rw [← Bridge.native_zplus] at h_v14
          step as ⟨e_v15, he_v15⟩
          store_step with Store.native_spec_zlt s9 e_v15 (by rw [he_v15]; rfl) h_v10 h_v14 hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
          rw [← Bridge.native_zlt] at h_v15
          have h_ite_v23 := (show if_0_eo__24smtx_5ftypeof_5fextract s10 v15 v1 v3 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_0_eo__24smtx_5ftypeof_5fextract
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s10
            rcases Store.boolean_value_native h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
            · ite_branch hbv_16
              try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
              store_step with Store.raw_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
              step as ⟨e_v17, he_v17⟩
              store_step with Store.native_spec_zplus s11 e_v17 (by rw [he_v17]; rfl) h_v1 h_v16 hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
              rw [← Bridge.native_zplus] at h_v17
              step as ⟨e_v18, he_v18⟩
              store_step with Store.native_spec_zneg s12 e_v18 (by rw [he_v18]; rfl) h_v3 hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
              rw [← Bridge.native_zneg] at h_v18
              step as ⟨e_v19, he_v19⟩
              store_step with Store.native_spec_zplus s13 e_v19 (by rw [he_v19]; rfl) h_v17 h_v18 hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
              rw [← Bridge.native_zplus] at h_v19
              step as ⟨e_v20, he_v20⟩
              store_step with Store.native_spec_int_to_nat s14 e_v20 (by rw [he_v20]; rfl) h_v19 hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
              rw [← Bridge.native_int_to_nat] at h_v20
              step as ⟨e_v21, he_v21⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eBitVec.construct s15 e_v21 (by rw [he_v21]; rfl) h_v20 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
              ite_done hinv16 hG with (native_ite_true_rep _ hx_16 h_v21)
            · ite_branch hbv_16
              step as ⟨e_v22, he_v22⟩
              store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s10 e_v22 (by rw [he_v22]; exact empty_args) hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
              ite_done hinv11 hG with (native_ite_false_rep _ hx_16 h_v22))
          store_step with h_ite_v23 as ⟨v23, s11, hinv11, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
          ite_done hinv11 hG with (native_ite_true_rep _ hx_10 h_v23)
        · ite_branch hbv_10
          step as ⟨e_v24, he_v24⟩
          store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s4 e_v24 (by rw [he_v24]; exact empty_args) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
          ite_done hinv5 hG with (native_ite_false_rep _ hx_10 h_v24))
      store_step with h_ite_v25 as ⟨v25, s5, hinv5, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7 h_v8 h_v9
      ite_done hinv5 hG with (native_ite_true_rep _ hx_8 h_v25)
    · ite_branch hbv_8
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s2 e_v26 (by rw [he_v26]; exact empty_args) hinv2 h64 as ⟨v26, s3, hinv3, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
      ite_done hinv3 hG with (native_ite_false_rep _ hx_8 h_v26))
  store_step with h_ite_v27 as ⟨v27, s3, hinv3, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v5 h_v6 h_v7
  case_done hinv3 hG with h_v27 in EoCases.__smtx_typeof_extract.case_0 using

theorem case_1_eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    case_1_eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__smtx_typeof_extract.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__smtx_typeof_extract.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24smtx_5ftypeof_5fextract
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5ftsm_2eNone.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__smtx_typeof_extract.case_1 using

/-- logos's `__smtx_typeof_extract` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24smtx_5ftypeof_5fextract.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __smtx_typeof_extract x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__smtx_typeof_extract.case_0 x_a0 x_a1 x_a2, EoCases.__smtx_typeof_extract.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __smtx_typeof_extract
  unfold EoCases.__smtx_typeof_extract.case_0 EoCases.__smtx_typeof_extract.case_1
  logos_eq

theorem body_eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24smtx_5ftypeof_5fextract s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__smtx_typeof_extract x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24smtx_5ftypeof_5fextract.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24smtx_5ftypeof_5fextract
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24smtx_5ftypeof_5fextract_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24smtx_5ftypeof_5fextract_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__smtx_typeof_extract.case_0 EoCases.__smtx_typeof_extract.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24smtx_5ftypeof_5fextract_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24smtx_5ftypeof_5fextract.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24smtx_5ftypeof_5fextract
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24smtx_5ftypeof_5fextract s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__smtx_typeof_extract x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24smtx_5ftypeof_5fextract_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
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
  rw [← Bridge.native_zleq] at h_v4
  have h_ite_v8 := (show if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv s3 v4 v1 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24smtx_5ftypeof_5fint_5fto_5fbv
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      step as ⟨e_v5, he_v5⟩
      store_step with Store.native_spec_int_to_nat s3 e_v5 (by rw [he_v5]; rfl) h_v1 hinv3 h64 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      rw [← Bridge.native_int_to_nat] at h_v5
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
  rw [← Bridge.native_and] at h_v8
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
  rw [← Bridge.native_zleq] at h_v4
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
  rw [← Bridge.native_zleq] at h_v6
  have h_ite_v13 := (show if_1_eo__24smtx_5ftypeof_5fre_2eloop s3 v6 v3 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24smtx_5ftypeof_5fre_2eloop
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_native h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.raw_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6
      step as ⟨e_v8, he_v8⟩
      store_step with Store.native_spec_zleq s4 e_v8 (by rw [he_v8]; rfl) h_v7 h_v3 hinv4 h64 as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
      rw [← Bridge.native_zleq] at h_v8
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
  rw [← Bridge.native_zleq] at h_v5
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
  rw [← Bridge.native_zleq] at h_v5
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

end pathos_compiled_checker
