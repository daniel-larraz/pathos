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

theorem case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  pat_destruct CtorSpec.eo_is.destruct h_v8 as ⟨v11, x_v11, h_v11⟩ else hinv1 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  obtain hn_v11 := CtorSpec.eo_is.fields_ne_stuck hinv1 h_v8
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v4 h_v5 h_v6 h_v8 hinv1 s1 v4 v5 v6 v8
  pat_same v2 v12 with h_v2 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v9 h_v11 dropping h_v12 h_v2 he_v13 hinv2 e_v13 s2 v12 v2
  store_step with ih.eo__24eo_5ftypeof s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v9 h_v11 h_v13 dropping hinv3 s3
  store_step with ih.eo__24dt_5fget_5fconstructors s4 v14 _ hinv4 h64 (hG.rem hrem) h_v14 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v9 h_v11 h_v13 dropping h_v14 hinv4 s4 v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s5 e_v16 (by rw [he_v16]; rfl) h_v13 h_v15 hinv5 h64 (hG.rem hrem) (by not_left_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v9 h_v11 dropping h_v13 h_v15 he_v16 hinv5 e_v16 s5 v13 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v9 h_v11 h_v16 dropping hinv6 s6
  have h_req_v24 := (show requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s7 v16 v17 v11 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v16 v17 with h_v16 h_v17 using hinv7 hG
    req_stuck h_v16 as hq_v16 using hinv7 hG
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v9 h_v11 dropping h_v16 h_v17 he_v18 hinv7 e_v18 s7 v16 v17
    step as ⟨e_v19, he_v19⟩
    store_step with CtorSpec.eo_is.construct s8 e_v19 (by rw [he_v19]; rfl) h_v11 hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v9 h_v18 dropping h_v11 he_v19 hinv8 e_v19 s8 v11
    store_step with Store.apply_rep s9 v19 v9 _ _ hinv9 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v18 dropping h_v19 h_v9 hinv9 s9 v19 v9
    store_step with Store.apply_rep s10 v18 v20 _ _ hinv10 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying dropping h_v18 h_v20 hinv10 s10 v18 v20
    store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v21 dropping hinv11 s11
    store_step with Store.apply_rep s12 v21 v22 _ _ hinv12 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying dropping h_v21 h_v22 hinv12 s12 v21 v22
    req_done hinv13 hG with h_v23 using hq_v16)
  store_step with h_req_v24 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying dropping h_req_v24 h_v11 h_v16 h_v17 h_v9 hinv7 s7 v11 v16 v17 v9
  case_done hinv14 hG with h_v24 in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11

/-- logos's `__eo_prog_dt_collapse_tester_singleton` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_collapse_tester_singleton x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_collapse_tester_singleton.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_collapse_tester_singleton
  unfold EoCases.__eo_prog_dt_collapse_tester_singleton.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_collapse_tester_singleton x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_collapse_tester_singleton.case_0

theorem eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_collapse_tester_singleton x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_collapse_updater.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_collapse_updater.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_updater.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_collapse_updater.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_collapse_updater.case_0
  store_step with ih.eo__24mk_5fdt_5fcollapse_5fupdater_5frhs s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  have h_req_v11 := (show requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s2 v7 v2 v5 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    req_same v7 v2 with h_v7 h_v2 using hinv2 hG
    req_stuck h_v7 as hq_v7 using hinv2 hG
    step as ⟨e_v8, he_v8⟩
    store_step with CtorSpec.eo__3d.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 dropping h_v7 he_v8 hinv2 e_v8 s2 v7
    store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 dropping h_v5 h_v8 hinv3 s3 v5 v8
    store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v2 h_v9 hinv4 s4 v2 v9
    req_done hinv5 hG with h_v10 using hq_v7)
  store_step with h_req_v11 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying dropping h_req_v11 h_v2 h_v5 h_v7 hinv2 s2 v2 v5 v7
  case_done hinv6 hG with h_v11 in EoCases.__eo_prog_dt_collapse_updater.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_dt_collapse_updater` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcollapse_2dupdater.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_collapse_updater x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_collapse_updater.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_collapse_updater
  unfold EoCases.__eo_prog_dt_collapse_updater.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_collapse_updater x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcollapse_2dupdater.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_collapse_updater.case_0

theorem eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcollapse_2dupdater.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcollapse_2dupdater
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_collapse_updater x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcons_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_cons_eq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_cons_eq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcons_2deq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_cons_eq.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  store_step with ih.eo__24mk_5fdt_5fcons_5feq s3 v12 v9 _ _ hinv3 h64 (hG.rem hrem) h_v12 h_v9 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 h_v14 dropping hinv3 s3
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s4 e_v16 (by rw [he_v16]; rfl) h_v14 h_v15 hinv4 h64 (hG.rem hrem) op_not_left_eo_and op_nil_apply_eo_and as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 h_v15 he_v16 hinv4 e_v16 s4 v14 v15
  have h_req_v23 := (show requires_0_eo__24eo_5fprog_5fdt_2dcons_2deq s5 v16 v2 v12 v9 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcons_2deq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v16 v2 with h_v16 h_v2 using hinv5 hG
    req_stuck h_v16 as hq_v16 using hinv5 hG
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v16 he_v17 hinv5 e_v17 s5 v16
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__3d.construct s6 e_v18 (by rw [he_v18]; exact empty_args) hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v12 h_v17 dropping he_v18 hinv6 e_v18 s6
    store_step with Store.apply_rep s7 v18 v12 _ _ hinv7 h64 h_v18 h_v12 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v17 dropping h_v12 h_v18 hinv7 s7 v12 v18
    store_step with Store.apply_rep s8 v19 v9 _ _ hinv8 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v17 dropping h_v19 h_v9 hinv8 s8 v19 v9
    store_step with Store.apply_rep s9 v17 v20 _ _ hinv9 h64 h_v17 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 dropping h_v17 h_v20 hinv9 s9 v17 v20
    store_step with Store.apply_rep s10 v21 v2 _ _ hinv10 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying dropping h_v2 h_v21 hinv10 s10 v2 v21
    req_done hinv11 hG with h_v22 using hq_v16)
  store_step with h_req_v23 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying dropping h_req_v23 h_v12 h_v16 h_v2 h_v9 hinv5 s5 v12 v16 v2 v9
  case_done hinv12 hG with h_v23 in EoCases.__eo_prog_dt_cons_eq.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_cons_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcons_2deq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_cons_eq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_cons_eq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_cons_eq
  unfold EoCases.__eo_prog_dt_cons_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcons_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcons_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_cons_eq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcons_2deq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcons_2deq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_cons_eq.case_0

theorem eo__24eo_5fprog_5fdt_2dcons_2deq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcons_2deq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcons_2deq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcons_2deq s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_cons_eq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcons_2deq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_cons_eq_clash.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_cons_eq_clash.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  pat_same v2 v14 with h_v2 h_v14 using hinv3 else hinv3 hG in EoCases.__eo_prog_dt_cons_eq_clash.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_eq s3 e_v15 (by rw [he_v15]; rfl) h_v12 h_v9 hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v9 h_v12 dropping h_v14 h_v2 he_v15 hinv3 e_v15 s3 v14 v2
  have h_ite_v19 := (show if_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s4 v15 v12 v9 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_v15 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v9 h_v12 dropping h_v15 v15
      ite_done hinv5 hG with (eo_ite_true_rep _ hx_16 h_v16)
    · ite_branch hbv_16
      store_step with ih.eo__24eo_5ftypeof s4 v12 _ hinv4 h64 (hG.rem hrem) h_v12 as ⟨v17, s5, hinv5, h_v17⟩ growing hG carrying h_v9 h_v12 dropping h_v15 v15
      store_step with ih.eo__24are_5fdistinct_5fterms_5ftype s5 v12 v9 v17 _ _ _ hinv5 h64 (hG.rem hrem) h_v12 h_v9 h_v17 as ⟨v18, s6, hinv6, h_v18⟩ growing hG carrying h_v9 h_v12 dropping h_v17 v17
      ite_done hinv6 hG with (eo_ite_false_rep _ hx_16 h_v18)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v19 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_v9 h_v12 dropping h_ite_v19 h_v15 hinv4 s4 v15
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v20, s6, hinv6, h_v20⟩ growing hG carrying h_v9 h_v12 h_v19 dropping hinv5 s5
  have h_req_v28 := (show requires_1_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s6 v19 v20 v12 v9 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v19 v20 with h_v19 h_v20 using hinv6 hG
    req_stuck h_v19 as hq_v19 using hinv6 hG
    step as ⟨e_v21, he_v21⟩
    store_step with CtorSpec.eo__3d.construct s6 e_v21 (by rw [he_v21]; exact empty_args) hinv6 h64 as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v9 h_v12 dropping h_v19 h_v20 he_v21 hinv6 e_v21 s6 v19 v20
    step as ⟨e_v22, he_v22⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v22 (by rw [he_v22]; exact empty_args) hinv7 h64 as ⟨v22, s8, hinv8, h_v22⟩ growing hG carrying h_v9 h_v12 h_v21 dropping he_v22 hinv7 e_v22 s7
    store_step with Store.apply_rep s8 v22 v12 _ _ hinv8 h64 h_v22 h_v12 (by ns_tac) (by ns_tac) as ⟨v23, s9, hinv9, h_v23⟩ growing hG carrying h_v9 h_v21 dropping h_v12 h_v22 hinv8 s8 v12 v22
    store_step with Store.apply_rep s9 v23 v9 _ _ hinv9 h64 h_v23 h_v9 (by ns_tac) (by ns_tac) as ⟨v24, s10, hinv10, h_v24⟩ growing hG carrying h_v21 dropping h_v23 h_v9 hinv9 s9 v23 v9
    store_step with Store.apply_rep s10 v21 v24 _ _ hinv10 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s11, hinv11, h_v25⟩ growing hG carrying dropping h_v21 h_v24 hinv10 s10 v21 v24
    store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v26, s12, hinv12, h_v26⟩ growing hG carrying h_v25 dropping hinv11 s11
    store_step with Store.apply_rep s12 v25 v26 _ _ hinv12 h64 h_v25 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s13, hinv13, h_v27⟩ growing hG carrying dropping h_v25 h_v26 hinv12 s12 v25 v26
    req_done hinv13 hG with h_v27 using hq_v19)
  store_step with h_req_v28 as ⟨v28, s14, hinv14, h_v28⟩ growing hG carrying dropping h_req_v28 h_v12 h_v19 h_v20 h_v9 hinv6 s6 v12 v19 v20 v9
  case_done hinv14 hG with h_v28 in EoCases.__eo_prog_dt_cons_eq_clash.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_cons_eq_clash` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_cons_eq_clash x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_cons_eq_clash.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_cons_eq_clash
  unfold EoCases.__eo_prog_dt_cons_eq_clash.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_cons_eq_clash x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_cons_eq_clash.case_0

theorem eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_cons_eq_clash x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dcycle s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_cycle.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_cycle.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dcycle
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cycle.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_cycle.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cycle.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cycle.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_cycle.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_cycle.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  pat_same v2 v14 with h_v2 h_v14 using hinv3 else hinv3 hG in EoCases.__eo_prog_dt_cycle.case_0
  store_step with ih.eo__24is_5fcons_5fapp s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v9 h_v12 dropping h_v14 h_v2 hinv3 s3 v14 v2
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v9 h_v12 h_v15 dropping hinv4 s4
  store_step with ih.eo__24dt_5ffind_5fcycle s5 v9 v12 v15 v16 _ _ _ _ hinv5 h64 (hG.rem hrem) h_v9 h_v12 h_v15 h_v16 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v9 h_v12 dropping h_v15 h_v16 hinv5 s5 v15 v16
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v9 h_v12 h_v17 dropping hinv6 s6
  have h_req_v26 := (show requires_0_eo__24eo_5fprog_5fdt_2dcycle s7 v17 v18 v12 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dcycle
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v17 v18 with h_v17 h_v18 using hinv7 hG
    req_stuck h_v17 as hq_v17 using hinv7 hG
    step as ⟨e_v19, he_v19⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v9 h_v12 dropping h_v17 h_v18 he_v19 hinv7 e_v19 s7 v17 v18
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__3d.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v9 h_v12 h_v19 dropping he_v20 hinv8 e_v20 s8
    store_step with Store.apply_rep s9 v20 v12 _ _ hinv9 h64 h_v20 h_v12 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v9 h_v19 dropping h_v12 h_v20 hinv9 s9 v12 v20
    store_step with Store.apply_rep s10 v21 v9 _ _ hinv10 h64 h_v21 h_v9 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v19 dropping h_v21 h_v9 hinv10 s10 v21 v9
    store_step with Store.apply_rep s11 v19 v22 _ _ hinv11 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying dropping h_v19 h_v22 hinv11 s11 v19 v22
    store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v23 dropping hinv12 s12
    store_step with Store.apply_rep s13 v23 v24 _ _ hinv13 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying dropping h_v23 h_v24 hinv13 s13 v23 v24
    req_done hinv14 hG with h_v25 using hq_v17)
  store_step with h_req_v26 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying dropping h_req_v26 h_v12 h_v17 h_v18 h_v9 hinv7 s7 v12 v17 v18 v9
  case_done hinv15 hG with h_v26 in EoCases.__eo_prog_dt_cycle.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_cycle` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dcycle.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_cycle x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_cycle.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_cycle
  unfold EoCases.__eo_prog_dt_cycle.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dcycle_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dcycle s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_cycle x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dcycle.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dcycle
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dcycle_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_cycle.case_0

theorem eo__24eo_5fprog_5fdt_2dcycle_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dcycle.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dcycle
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dcycle s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_cycle x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dcycle_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dinst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dinst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_inst.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_inst.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dinst
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_inst.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_inst.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_inst.case_0
  pat_unapply h_v2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_inst.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_inst.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v5 h_v9 h_v11 h_v12 dropping h_v2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v2 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_dt_inst.case_0
  store_step with ih.eo__24mk_5fdt_5finst_5fprem s2 v5 v12 _ _ hinv2 h64 (hG.rem hrem) h_v5 h_v12 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v5 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  have h_req_v21 := (show requires_0_eo__24eo_5fprog_5fdt_2dinst s3 v14 v9 v5 v12 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dinst
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v14 v9 with h_v14 h_v9 using hinv3 hG
    req_stuck h_v14 as hq_v14 using hinv3 hG
    step as ⟨e_v15, he_v15⟩
    store_step with CtorSpec.eo__3d.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v5 h_v9 h_v12 dropping h_v14 he_v15 hinv3 e_v15 s3 v14
    store_step with Store.apply_rep s4 v15 v5 _ _ hinv4 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v9 h_v12 dropping h_v15 h_v5 hinv4 s4 v15 v5
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v9 h_v12 h_v16 dropping he_v17 hinv5 e_v17 s5
    store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v9 h_v16 dropping h_v12 h_v17 hinv6 s6 v12 v17
    store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v16 dropping h_v18 h_v9 hinv7 s7 v18 v9
    store_step with Store.apply_rep s8 v16 v19 _ _ hinv8 h64 h_v16 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying dropping h_v16 h_v19 hinv8 s8 v16 v19
    req_done hinv9 hG with h_v20 using hq_v14)
  store_step with h_req_v21 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_req_v21 h_v12 h_v14 h_v5 h_v9 hinv3 s3 v12 v14 v5 v9
  case_done hinv10 hG with h_v21 in EoCases.__eo_prog_dt_inst.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_inst` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dinst.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_inst x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_inst.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_inst
  unfold EoCases.__eo_prog_dt_inst.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dinst_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dinst s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_inst x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dinst.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dinst
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dinst_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_inst.case_0

theorem eo__24eo_5fprog_5fdt_2dinst_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dinst.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dinst
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dinst s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_inst x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dinst_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_updater_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_updater_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_updater_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_dt_updater_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_updater_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_updater_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_dt_updater_elim.case_0
  store_step with Store.apply_rep s1 v11 v12 _ _ hinv1 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 hinv1 s1 v4 v5 v6 v8
  store_step with Store.apply_rep s2 v13 v9 _ _ hinv2 h64 h_v13 h_v9 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v13 hinv2 s2 v13
  store_step with ih.eo__24mk_5fdt_5fupdater_5felim_5fconc s3 v14 v2 _ _ hinv3 h64 (hG.rem hrem) h_v14 h_v2 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v14 hinv3 s3 v14
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping hinv4 s4
  have h_req_v22 := (show requires_0_eo__24eo_5fprog_5fdt_2dupdater_2delim s5 v15 v16 v11 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fdt_2dupdater_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v15 v16 with h_v15 h_v16 using hinv5 hG
    req_stuck h_v15 as hq_v15 using hinv5 hG
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v15 h_v16 he_v17 hinv5 e_v17 s5 v15 v16
    store_step with Store.apply_rep s6 v11 v12 _ _ hinv6 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v17 dropping h_v11 h_v12 hinv6 s6 v11 v12
    store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v17 dropping h_v18 h_v9 hinv7 s7 v18 v9
    store_step with Store.apply_rep s8 v17 v19 _ _ hinv8 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 dropping h_v17 h_v19 hinv8 s8 v17 v19
    store_step with Store.apply_rep s9 v20 v2 _ _ hinv9 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_v2 h_v20 hinv9 s9 v2 v20
    req_done hinv10 hG with h_v21 using hq_v15)
  store_step with h_req_v22 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying dropping h_req_v22 h_v11 h_v12 h_v15 h_v16 h_v2 h_v9 hinv5 s5 v11 v12 v15 v16 v2 v9
  case_done hinv11 hG with h_v22 in EoCases.__eo_prog_dt_updater_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_dt_updater_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_2dupdater_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_updater_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_updater_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_updater_elim
  unfold EoCases.__eo_prog_dt_updater_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_2dupdater_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_updater_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_2dupdater_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_2dupdater_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_updater_elim.case_0

theorem eo__24eo_5fprog_5fdt_2dupdater_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_2dupdater_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_2dupdater_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_2dupdater_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_updater_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_2dupdater_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fdt_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_dt_split.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_dt_split.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fdt_5fsplit
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  store_step with ih.eo__24eo_5ftypeof s1 a0 _ hinv1 h64 (hG.rem hrem) h_a0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping hinv1 s1
  store_step with ih.eo__24dt_5fget_5fconstructors s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with ih.eo__24mk_5fdt_5fsplit s3 v2 a0 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a0 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s4 e_v4 (by rw [he_v4]; rfl) h_v0 h_v3 hinv4 h64 (hG.rem hrem) op_not_left_eo_or op_nil_apply_eo_or as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 he_v4 hinv4 e_v4 s4 v0 v3
  case_done hinv5 hG with h_v4 in EoCases.__eo_prog_dt_split.case_0 using hn_a0

/-- logos's `__eo_prog_dt_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fdt_5fsplit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_dt_split x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_dt_split.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_dt_split
  unfold EoCases.__eo_prog_dt_split.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fdt_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fdt_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_dt_split x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fdt_5fsplit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fdt_5fsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fdt_5fsplit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_dt_split.case_0

theorem eo__24eo_5fprog_5fdt_5fsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fdt_5fsplit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fdt_5fsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fdt_5fsplit s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_dt_split x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fdt_5fsplit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_cond_deq.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_cond_deq.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_cond_deq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_eq_cond_deq.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping he_v19 hinv5 e_v19 s5
  store_step with Store.apply_rep s6 v19 a0 _ _ hinv6 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v18 v21 _ _ hinv8 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 h_v21 hinv8 s8 v18 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v23 (by rw [he_v23]; exact empty_args) hinv9 h64 as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v22 dropping he_v23 hinv9 e_v23 s9
  store_step with Store.apply_rep s10 v23 a0 _ _ hinv10 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v22 dropping h_v23 hinv10 s10 v23
  store_step with Store.apply_rep s11 v24 a2 _ _ hinv11 h64 h_v24 h_a2 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v22 dropping h_v24 hinv11 s11 v24
  store_step with Store.apply_rep s12 v22 v25 _ _ hinv12 h64 h_v22 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v22 h_v25 hinv12 s12 v22 v25
  store_step with Store.apply_rep s13 v17 v26 _ _ hinv13 h64 h_v17 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v17 h_v26 hinv13 s13 v17 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_and.construct s14 e_v28 (by rw [he_v28]; exact empty_args) hinv14 h64 as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 dropping he_v28 hinv14 e_v28 s14
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_not.construct s15 e_v29 (by rw [he_v29]; exact empty_args) hinv15 h64 as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 h_v28 dropping he_v29 hinv15 e_v29 s15
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v30 (by rw [he_v30]; exact empty_args) hinv16 h64 as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 h_v28 h_v29 dropping he_v30 hinv16 e_v30 s16
  store_step with Store.apply_rep s17 v30 a0 _ _ hinv17 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v27 h_v28 h_v29 dropping h_v30 hinv17 s17 v30
  store_step with Store.apply_rep s18 v31 a1 _ _ hinv18 h64 h_v31 h_a1 (by ns_tac) (by ns_tac) as ⟨v32, s19, hinv19, h_v32⟩ growing hG carrying h_a0 h_a2 h_v27 h_v28 h_v29 dropping h_a1 h_v31 hinv18 s18 v31
  store_step with Store.apply_rep s19 v29 v32 _ _ hinv19 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s20, hinv20, h_v33⟩ growing hG carrying h_a0 h_a2 h_v27 h_v28 dropping h_v29 h_v32 hinv19 s19 v29 v32
  store_step with Store.apply_rep s20 v28 v33 _ _ hinv20 h64 h_v28 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s21, hinv21, h_v34⟩ growing hG carrying h_a0 h_a2 h_v27 dropping h_v28 h_v33 hinv20 s20 v28 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_and.construct s21 e_v35 (by rw [he_v35]; exact empty_args) hinv21 h64 as ⟨v35, s22, hinv22, h_v35⟩ growing hG carrying h_a0 h_a2 h_v27 h_v34 dropping he_v35 hinv21 e_v35 s21
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_not.construct s22 e_v36 (by rw [he_v36]; exact empty_args) hinv22 h64 as ⟨v36, s23, hinv23, h_v36⟩ growing hG carrying h_a0 h_a2 h_v27 h_v34 h_v35 dropping he_v36 hinv22 e_v36 s22
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v37 (by rw [he_v37]; exact empty_args) hinv23 h64 as ⟨v37, s24, hinv24, h_v37⟩ growing hG carrying h_a0 h_a2 h_v27 h_v34 h_v35 h_v36 dropping he_v37 hinv23 e_v37 s23
  store_step with Store.apply_rep s24 v37 a0 _ _ hinv24 h64 h_v37 h_a0 (by ns_tac) (by ns_tac) as ⟨v38, s25, hinv25, h_v38⟩ growing hG carrying h_a2 h_v27 h_v34 h_v35 h_v36 dropping h_a0 h_v37 hinv24 s24 v37
  store_step with Store.apply_rep s25 v38 a2 _ _ hinv25 h64 h_v38 h_a2 (by ns_tac) (by ns_tac) as ⟨v39, s26, hinv26, h_v39⟩ growing hG carrying h_v27 h_v34 h_v35 h_v36 dropping h_a2 h_v38 hinv25 s25 v38
  store_step with Store.apply_rep s26 v36 v39 _ _ hinv26 h64 h_v36 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s27, hinv27, h_v40⟩ growing hG carrying h_v27 h_v34 h_v35 dropping h_v36 h_v39 hinv26 s26 v36 v39
  store_step with Store.apply_rep s27 v35 v40 _ _ hinv27 h64 h_v35 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s28, hinv28, h_v41⟩ growing hG carrying h_v27 h_v34 dropping h_v35 h_v40 hinv27 s27 v35 v40
  store_step with Store.literal_boolean_spec s28 true hinv28 h64 as ⟨v42, s29, hinv29, h_v42⟩ growing hG carrying h_v27 h_v34 h_v41 dropping hinv28 s28
  store_step with Store.apply_rep s29 v41 v42 _ _ hinv29 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s30, hinv30, h_v43⟩ growing hG carrying h_v27 h_v34 dropping h_v41 h_v42 hinv29 s29 v41 v42
  store_step with Store.apply_rep s30 v34 v43 _ _ hinv30 h64 h_v34 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s31, hinv31, h_v44⟩ growing hG carrying h_v27 dropping h_v34 h_v43 hinv30 s30 v34 v43
  store_step with Store.apply_rep s31 v27 v44 _ _ hinv31 h64 h_v27 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s32, hinv32, h_v45⟩ growing hG carrying dropping h_v27 h_v44 hinv31 s31 v27 v44
  case_done hinv32 hG with h_v45 in EoCases.__eo_prog_eq_cond_deq.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_eq_cond_deq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2dcond_2ddeq.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_cond_deq.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_cond_deq
  unfold EoCases.__eo_prog_eq_cond_deq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5feq_2dcond_2ddeq s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2dcond_2ddeq.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5feq_2dcond_2ddeq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_eq_cond_deq.case_0

theorem eo__24eo_5fprog_5feq_2dcond_2ddeq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2dcond_2ddeq.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5feq_2dcond_2ddeq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2dcond_2ddeq s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_eq_cond_deq x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2dcond_2ddeq_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2dite_2dlift_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_ite_lift.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_ite_lift.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2dite_2dlift
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v7 hinv8 s8 v0 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_a2 h_a3 h_v8 dropping h_a0 h_v9 hinv10 s10 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a2 h_a3 h_v8 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a2 h_a3 h_v8 h_v10 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a2 h_a3 h_v8 h_v10 dropping h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v10 v13 _ _ hinv14 h64 h_v10 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a2 h_a3 h_v8 dropping h_v10 h_v13 hinv14 s14 v10 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_a3 h_v8 h_v14 dropping he_v15 hinv15 e_v15 s15
  store_step with Store.apply_rep s16 v15 a2 _ _ hinv16 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a3 h_v8 h_v14 dropping h_a2 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v16 a3 _ _ hinv17 h64 h_v16 h_a3 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v8 h_v14 dropping h_a3 h_v16 hinv17 s17 v16
  store_step with Store.apply_rep s18 v14 v17 _ _ hinv18 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_v8 dropping h_v14 h_v17 hinv18 s18 v14 v17
  store_step with Store.apply_rep s19 v8 v18 _ _ hinv19 h64 h_v8 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying dropping h_v18 h_v8 hinv19 s19 v18 v8
  case_done hinv20 hG with h_v19 in EoCases.__eo_prog_eq_ite_lift.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_eq_ite_lift` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2dite_2dlift.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_ite_lift.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_ite_lift
  unfold EoCases.__eo_prog_eq_ite_lift.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2dite_2dlift_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5feq_2dite_2dlift s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2dite_2dlift.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5feq_2dite_2dlift
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2dite_2dlift_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_eq_ite_lift.case_0

theorem eo__24eo_5fprog_5feq_2dite_2dlift_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2dite_2dlift.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5feq_2dite_2dlift
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2dite_2dlift s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_eq_ite_lift x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2dite_2dlift_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2drefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_refl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_refl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2drefl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv6 s6 v4 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_eq_refl.case_0 using hn_a0

/-- logos's `__eo_prog_eq_refl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2drefl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_eq_refl x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_refl.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_refl
  unfold EoCases.__eo_prog_eq_refl.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2drefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5feq_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_refl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2drefl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5feq_2drefl
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2drefl_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_eq_refl.case_0

theorem eo__24eo_5fprog_5feq_2drefl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2drefl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5feq_2drefl
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2drefl s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_eq_refl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2drefl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_2dsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5feq_2dsymm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_symm.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_symm.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_2dsymm
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_a1 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v4 h_v7 hinv8 s8 v4 v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_eq_symm.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_eq_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_2dsymm.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_eq_symm x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_eq_symm.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_symm
  unfold EoCases.__eo_prog_eq_symm.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_2dsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5feq_2dsymm s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_symm x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_2dsymm.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5feq_2dsymm
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5feq_2dsymm_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_eq_symm.case_0

theorem eo__24eo_5fprog_5feq_2dsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_2dsymm.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5feq_2dsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_2dsymm s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_eq_symm x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_2dsymm_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5feq_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fprog_5feq_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_eq_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_eq_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5feq_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_unapply h_v3 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv else hinv hG in EoCases.__eo_prog_eq_resolve.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s e_v10 (by rw [he_v10]; exact empty_args) hinv h64 as ⟨v10, s1, hinv1, h_v10⟩ growing hG carrying h_v1 h_v6 h_v8 h_v9 dropping h_a0 h_a1 h_v3 h_v5 he_v10 e_v10 v3 v5
  pat_same v8 v10 with h_v8 h_v10 using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_resolve.case_0
  pat_same v9 v1 with h_v9 h_v1 using hinv1 else hinv1 hG in EoCases.__eo_prog_eq_resolve.case_0
  case_done hinv1 hG with h_v6 in EoCases.__eo_prog_eq_resolve.case_0 using hn_v5 hn_v6 hn_v8 hn_v9

/-- logos's `__eo_prog_eq_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5feq_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_eq_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_prog_eq_resolve.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_eq_resolve
  unfold EoCases.__eo_prog_eq_resolve.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5feq_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5feq_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_eq_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5feq_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5feq_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5feq_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_eq_resolve.case_0

theorem eo__24eo_5fprog_5feq_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5feq_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5feq_5fresolve
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5feq_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_eq_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5feq_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_equiv_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_equiv_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fequiv_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_equiv_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_equiv_elim1.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 h_v7 h_v9 dropping he_v10 hinv2 e_v10 s2
  store_step with Store.apply_rep s3 v10 v7 _ _ hinv3 h64 h_v10 h_v7 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v4 h_v9 dropping h_v10 h_v7 hinv3 s3 v10 v7
  store_step with Store.apply_rep s4 v9 v11 _ _ hinv4 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v4 dropping h_v11 h_v9 hinv4 s4 v11 v9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v4 h_v12 dropping he_v13 hinv5 e_v13 s5
  store_step with Store.apply_rep s6 v13 v4 _ _ hinv6 h64 h_v13 h_v4 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v12 dropping h_v13 h_v4 hinv6 s6 v13 v4
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v12 h_v14 dropping hinv7 s7
  store_step with Store.apply_rep s8 v14 v15 _ _ hinv8 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v12 dropping h_v14 h_v15 hinv8 s8 v14 v15
  store_step with Store.apply_rep s9 v12 v16 _ _ hinv9 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying dropping h_v12 h_v16 hinv9 s9 v12 v16
  case_done hinv10 hG with h_v17 in EoCases.__eo_prog_equiv_elim1.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_equiv_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fequiv_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_equiv_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_equiv_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_equiv_elim1
  unfold EoCases.__eo_prog_equiv_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_equiv_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fequiv_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fequiv_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fequiv_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_equiv_elim1.case_0

theorem eo__24eo_5fprog_5fequiv_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fequiv_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fequiv_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fequiv_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_equiv_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fequiv_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_equiv_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_equiv_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fequiv_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_equiv_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_equiv_elim2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_equiv_elim2.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  store_step with Store.apply_rep s2 v9 v7 _ _ hinv2 h64 h_v9 h_v7 (by ns_tac) (by ns_tac) as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 dropping h_v7 h_v9 hinv2 s2 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v4 h_v10 dropping he_v11 hinv3 e_v11 s3
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_not.construct s4 e_v12 (by rw [he_v12]; exact empty_args) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v4 h_v10 h_v11 dropping he_v12 hinv4 e_v12 s4
  store_step with Store.apply_rep s5 v12 v4 _ _ hinv5 h64 h_v12 h_v4 (by ns_tac) (by ns_tac) as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v10 h_v11 dropping h_v12 h_v4 hinv5 s5 v12 v4
  store_step with Store.apply_rep s6 v11 v13 _ _ hinv6 h64 h_v11 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v10 dropping h_v11 h_v13 hinv6 s6 v11 v13
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v10 h_v14 dropping hinv7 s7
  store_step with Store.apply_rep s8 v14 v15 _ _ hinv8 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v10 dropping h_v14 h_v15 hinv8 s8 v14 v15
  store_step with Store.apply_rep s9 v10 v16 _ _ hinv9 h64 h_v10 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying dropping h_v10 h_v16 hinv9 s9 v10 v16
  case_done hinv10 hG with h_v17 in EoCases.__eo_prog_equiv_elim2.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_equiv_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fequiv_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_equiv_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_equiv_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_equiv_elim2
  unfold EoCases.__eo_prog_equiv_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_equiv_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fequiv_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fequiv_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fequiv_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_equiv_elim2.case_0

theorem eo__24eo_5fprog_5fequiv_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fequiv_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fequiv_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fequiv_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_equiv_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fequiv_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fexists_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fexists_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_exists_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_exists_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fexists_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_exists.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s2 e_v17 (by rw [he_v17]; exact empty_args) hinv2 h64 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_v9 h_v12 h_v15 h_v16 dropping h_v11 h_v13 h_v2 he_v17 hinv2 e_v17 s2 v11 v13 v2
  pat_same v15 v17 with h_v15 h_v17 using hinv3 else hinv3 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v19 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_forall.construct s3 e_v24 (by rw [he_v24]; exact empty_args) hinv3 h64 as ⟨v24, s4, hinv4, h_v24⟩ growing hG carrying h_v9 h_v12 h_v20 h_v22 h_v23 dropping h_v15 h_v16 h_v17 h_v19 he_v24 hinv3 e_v24 s3 v15 v16 v17 v19
  pat_same v22 v24 with h_v22 h_v24 using hinv4 else hinv4 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_same v23 v12 with h_v23 h_v12 using hinv4 else hinv4 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_unapply h_v20 as ⟨v26, v27, x_v26, x_v27, h_v26, h_v27, hn_v26, hn_v27⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s4 e_v28 (by rw [he_v28]; exact empty_args) hinv4 h64 as ⟨v28, s5, hinv5, h_v28⟩ growing hG carrying h_v9 h_v12 h_v26 h_v27 dropping h_v20 h_v22 h_v23 h_v24 he_v28 hinv4 e_v28 s4 v20 v22 v23 v24
  pat_same v26 v28 with h_v26 h_v28 using hinv5 else hinv5 hG in EoCases.__eo_prog_exists_elim.case_0
  pat_same v27 v9 with h_v27 h_v9 using hinv5 else hinv5 hG in EoCases.__eo_prog_exists_elim.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v29 (by rw [he_v29]; exact empty_args) hinv5 h64 as ⟨v29, s6, hinv6, h_v29⟩ growing hG carrying h_v9 h_v12 dropping h_v26 h_v27 h_v28 he_v29 hinv5 e_v29 s5 v26 v27 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_exists.construct s6 e_v30 (by rw [he_v30]; exact empty_args) hinv6 h64 as ⟨v30, s7, hinv7, h_v30⟩ growing hG carrying h_v9 h_v12 h_v29 dropping he_v30 hinv6 e_v30 s6
  store_step with Store.apply_rep s7 v30 v12 _ _ hinv7 h64 h_v30 h_v12 (by ns_tac) (by ns_tac) as ⟨v31, s8, hinv8, h_v31⟩ growing hG carrying h_v9 h_v12 h_v29 dropping h_v30 hinv7 s7 v30
  store_step with Store.apply_rep s8 v31 v9 _ _ hinv8 h64 h_v31 h_v9 (by ns_tac) (by ns_tac) as ⟨v32, s9, hinv9, h_v32⟩ growing hG carrying h_v9 h_v12 h_v29 dropping h_v31 hinv8 s8 v31
  store_step with Store.apply_rep s9 v29 v32 _ _ hinv9 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s10, hinv10, h_v33⟩ growing hG carrying h_v9 h_v12 dropping h_v29 h_v32 hinv9 s9 v29 v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_not.construct s10 e_v34 (by rw [he_v34]; exact empty_args) hinv10 h64 as ⟨v34, s11, hinv11, h_v34⟩ growing hG carrying h_v9 h_v12 h_v33 dropping he_v34 hinv10 e_v34 s10
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_forall.construct s11 e_v35 (by rw [he_v35]; exact empty_args) hinv11 h64 as ⟨v35, s12, hinv12, h_v35⟩ growing hG carrying h_v9 h_v12 h_v33 h_v34 dropping he_v35 hinv11 e_v35 s11
  store_step with Store.apply_rep s12 v35 v12 _ _ hinv12 h64 h_v35 h_v12 (by ns_tac) (by ns_tac) as ⟨v36, s13, hinv13, h_v36⟩ growing hG carrying h_v9 h_v33 h_v34 dropping h_v12 h_v35 hinv12 s12 v12 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_not.construct s13 e_v37 (by rw [he_v37]; exact empty_args) hinv13 h64 as ⟨v37, s14, hinv14, h_v37⟩ growing hG carrying h_v9 h_v33 h_v34 h_v36 dropping he_v37 hinv13 e_v37 s13
  store_step with Store.apply_rep s14 v37 v9 _ _ hinv14 h64 h_v37 h_v9 (by ns_tac) (by ns_tac) as ⟨v38, s15, hinv15, h_v38⟩ growing hG carrying h_v33 h_v34 h_v36 dropping h_v37 h_v9 hinv14 s14 v37 v9
  store_step with Store.apply_rep s15 v36 v38 _ _ hinv15 h64 h_v36 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s16, hinv16, h_v39⟩ growing hG carrying h_v33 h_v34 dropping h_v36 h_v38 hinv15 s15 v36 v38
  store_step with Store.apply_rep s16 v34 v39 _ _ hinv16 h64 h_v34 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s17, hinv17, h_v40⟩ growing hG carrying h_v33 dropping h_v34 h_v39 hinv16 s16 v34 v39
  store_step with Store.apply_rep s17 v33 v40 _ _ hinv17 h64 h_v33 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s18, hinv18, h_v41⟩ growing hG carrying dropping h_v33 h_v40 hinv17 s17 v33 v40
  case_done hinv18 hG with h_v41 in EoCases.__eo_prog_exists_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v19 hn_v20 hn_v22 hn_v23 hn_v26 hn_v27

/-- logos's `__eo_prog_exists_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fexists_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_exists_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_exists_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_exists_elim
  unfold EoCases.__eo_prog_exists_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fexists_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fexists_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_exists_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fexists_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fexists_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fexists_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_exists_elim.case_0

theorem eo__24eo_5fprog_5fexists_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fexists_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fexists_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fexists_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_exists_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fexists_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fexists_5fstring_5flength_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fexists_5fstring_5flength s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_exists_string_length.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_exists_string_length.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fexists_5fstring_5flength
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_exists_string_length.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_a2 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_exists_string_length.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s1 1#u32 (-1) (by scalar_tac) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_gt s2 e_v5 (by rw [he_v5]; rfl) h_a1 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v4 he_v5 hinv2 e_v5 s2 v4
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v5 dropping hinv3 s3
  have h_req_v19 := (show requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength s4 v5 v6 a2 v2 a1 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v5 v6 with h_v5 h_v6 using hinv4 hG
    req_stuck h_v5 as hq_v5 using hinv4 hG
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_neg_u32_spec s4 1#u32 (-1) (by scalar_tac) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v5 h_v6 hinv4 s4 v5 v6
    step as ⟨e_v8, he_v8⟩
    store_step with Store.builtin_spec_gt s5 e_v8 (by rw [he_v8]; rfl) h_a2 h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v7 he_v8 hinv5 e_v8 s5 v7
    store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a1 h_a2 h_v2 h_v8 dropping hinv6 s6
    have h_req_v18 := (show requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength s7 v8 v9 v2 a1 a2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s7
      req_same v8 v9 with h_v8 h_v9 using hinv7 hG
      req_stuck h_v8 as hq_v8 using hinv7 hG
      step as ⟨e_v10, he_v10⟩
      store_step with CtorSpec.eo__3d.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v8 h_v9 he_v10 hinv7 e_v10 s7 v8 v9
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo_str_2elen.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a1 h_a2 h_v2 h_v10 dropping he_v11 hinv8 e_v11 s8
      step as ⟨e_v12, he_v12⟩
      store_step with CtorSpec.eo_Seq.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_a1 h_a2 h_v2 h_v10 h_v11 dropping he_v12 hinv9 e_v12 s9
      store_step with Store.apply_rep s10 v12 v2 _ _ hinv10 h64 h_v12 h_v2 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_a1 h_a2 h_v10 h_v11 dropping h_v12 h_v2 hinv10 s10 v12 v2
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo__40witness_5fstring_5flength.construct s11 e_v14 (by rw [he_v14]; rfl) h_v13 h_a1 h_a2 hinv11 h64 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_a1 h_v10 h_v11 dropping h_a2 h_v13 he_v14 hinv11 e_v14 s11 v13
      store_step with Store.apply_rep s12 v11 v14 _ _ hinv12 h64 h_v11 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_a1 h_v10 dropping h_v11 h_v14 hinv12 s12 v11 v14
      store_step with Store.apply_rep s13 v10 v15 _ _ hinv13 h64 h_v10 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_a1 dropping h_v10 h_v15 hinv13 s13 v10 v15
      store_step with Store.apply_rep s14 v16 a1 _ _ hinv14 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying dropping h_a1 h_v16 hinv14 s14 v16
      req_done hinv15 hG with h_v17 using hq_v8)
    store_step with h_req_v18 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying dropping h_a1 h_a2 h_req_v18 h_v2 h_v8 h_v9 hinv7 s7 v2 v8 v9
    req_done hinv16 hG with h_v18 using hq_v5)
  store_step with h_req_v19 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying dropping h_a1 h_req_v19 h_v2 h_v5 h_v6 hinv4 s4 v2 v5 v6
  case_done hinv17 hG with h_v19 in EoCases.__eo_prog_exists_string_length.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__eo_prog_exists_string_length` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fexists_5fstring_5flength.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_exists_string_length x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_exists_string_length.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_exists_string_length
  unfold EoCases.__eo_prog_exists_string_length.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fexists_5fstring_5flength_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fexists_5fstring_5flength s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_exists_string_length x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fexists_5fstring_5flength.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fexists_5fstring_5flength
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fexists_5fstring_5flength_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_exists_string_length.case_0

theorem eo__24eo_5fprog_5fexists_5fstring_5flength_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fexists_5fstring_5flength.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fexists_5fstring_5flength
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fexists_5fstring_5flength s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_exists_string_length x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fexists_5fstring_5flength_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ffactoring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ffactoring s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_factoring.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_factoring.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ffactoring
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_factoring.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_or.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_v1 dropping h_a0 he_v2 e_v2
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_list_setof n ih.eo__24eo_5fis_5flist_5fnil s1 e_v3 (by rw [he_v3]; rfl) h_v2 h_v1 hinv1 h64 (hG.rem hrem) op_not_left_eo_or as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying dropping h_v1 h_v2 he_v3 hinv1 e_v3 s1 v1 v2
  store_step with ih.eo__24from_5fclause s2 v3 _ hinv2 h64 (hG.rem hrem) h_v3 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_v3 hinv2 s2 v3
  case_done hinv3 hG with h_v4 in EoCases.__eo_prog_factoring.case_0 using

/-- logos's `__eo_prog_factoring` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ffactoring.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_factoring x_a0 =
      (firstSome [EoCases.__eo_prog_factoring.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_factoring
  unfold EoCases.__eo_prog_factoring.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ffactoring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ffactoring s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_factoring x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ffactoring.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ffactoring
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ffactoring_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_factoring.case_0

theorem eo__24eo_5fprog_5ffactoring_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ffactoring.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ffactoring
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ffactoring s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_factoring x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ffactoring_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ffalse_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ffalse_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_false_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_false_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ffalse_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_false_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_false_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_false_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_false_elim.case_0
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 hinv1 s1 v6 v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_false_elim.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v7 dropping h_v4 h_v9 he_v10 hinv2 e_v10 s2 v4 v9
  store_step with Store.apply_rep s3 v10 v7 _ _ hinv3 h64 h_v10 h_v7 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying dropping h_v10 h_v7 hinv3 s3 v10 v7
  case_done hinv4 hG with h_v11 in EoCases.__eo_prog_false_elim.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_false_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ffalse_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_false_elim x_a0 =
      (firstSome [EoCases.__eo_prog_false_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_false_elim
  unfold EoCases.__eo_prog_false_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ffalse_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ffalse_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_false_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ffalse_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ffalse_5felim
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ffalse_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_false_elim.case_0

theorem eo__24eo_5fprog_5ffalse_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ffalse_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ffalse_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ffalse_5felim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_false_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ffalse_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ffalse_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ffalse_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_false_intro.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_false_intro.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ffalse_5fintro
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_false_intro.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_false_intro.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_false_intro.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v4 dropping h_v3 h_v5 he_v6 hinv1 e_v6 s1 v3 v5
  store_step with Store.apply_rep s2 v6 v4 _ _ hinv2 h64 h_v6 h_v4 (by ns_tac) (by ns_tac) as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying dropping h_v4 h_v6 hinv2 s2 v4 v6
  store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_v7 dropping hinv3 s3
  store_step with Store.apply_rep s4 v7 v8 _ _ hinv4 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying dropping h_v7 h_v8 hinv4 s4 v7 v8
  case_done hinv5 hG with h_v9 in EoCases.__eo_prog_false_intro.case_0 using hn_v3 hn_v4

/-- logos's `__eo_prog_false_intro` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ffalse_5fintro.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_false_intro x_a0 =
      (firstSome [EoCases.__eo_prog_false_intro.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_false_intro
  unfold EoCases.__eo_prog_false_intro.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ffalse_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ffalse_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_false_intro x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ffalse_5fintro.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ffalse_5fintro
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ffalse_5fintro_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_false_intro.case_0

theorem eo__24eo_5fprog_5ffalse_5fintro_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ffalse_5fintro.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ffalse_5fintro
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ffalse_5fintro s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_false_intro x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ffalse_5fintro_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fho_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fho_5fcong s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ho_cong.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ho_cong.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fho_5fcong
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ho_cong.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ho_cong.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ho_cong.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_and.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_ho_cong.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_ho_cong.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_ho_cong.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_ho_cong.case_0
  store_step with ih.eo__24mk_5fho_5fcong s2 v14 v11 v4 _ _ _ hinv2 h64 (hG.rem hrem) h_v14 h_v11 h_v4 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying dropping h_v11 h_v13 h_v14 h_v15 h_v4 hinv2 s2 v11 v13 v14 v15 v4
  case_done hinv3 hG with h_v16 in EoCases.__eo_prog_ho_cong.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_ho_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fho_5fcong.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ho_cong x_a0 =
      (firstSome [EoCases.__eo_prog_ho_cong.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ho_cong
  unfold EoCases.__eo_prog_ho_cong.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fho_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fho_5fcong s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ho_cong x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fho_5fcong.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fho_5fcong
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fho_5fcong_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_ho_cong.case_0

theorem eo__24eo_5fprog_5fho_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fho_5fcong.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fho_5fcong
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fho_5fcong s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ho_cong x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fho_5fcong_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fimplies_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fimplies_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_implies_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_implies_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fimplies_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_implies_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_implies_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_implies_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_implies_elim.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 h_v7 h_v9 dropping he_v10 hinv2 e_v10 s2
  store_step with Store.apply_rep s3 v10 v7 _ _ hinv3 h64 h_v10 h_v7 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v4 h_v9 dropping h_v10 h_v7 hinv3 s3 v10 v7
  store_step with Store.apply_rep s4 v9 v11 _ _ hinv4 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_v4 dropping h_v11 h_v9 hinv4 s4 v11 v9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_v4 h_v12 dropping he_v13 hinv5 e_v13 s5
  store_step with Store.apply_rep s6 v13 v4 _ _ hinv6 h64 h_v13 h_v4 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_v12 dropping h_v13 h_v4 hinv6 s6 v13 v4
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_v12 h_v14 dropping hinv7 s7
  store_step with Store.apply_rep s8 v14 v15 _ _ hinv8 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_v12 dropping h_v14 h_v15 hinv8 s8 v14 v15
  store_step with Store.apply_rep s9 v12 v16 _ _ hinv9 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying dropping h_v12 h_v16 hinv9 s9 v12 v16
  case_done hinv10 hG with h_v17 in EoCases.__eo_prog_implies_elim.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_implies_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fimplies_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_implies_elim x_a0 =
      (firstSome [EoCases.__eo_prog_implies_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_implies_elim
  unfold EoCases.__eo_prog_implies_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fimplies_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fimplies_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_implies_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fimplies_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fimplies_5felim
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fimplies_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_implies_elim.case_0

theorem eo__24eo_5fprog_5fimplies_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fimplies_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fimplies_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fimplies_5felim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_implies_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fimplies_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5finstantiate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5finstantiate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_instantiate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_instantiate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5finstantiate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_instantiate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_instantiate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_instantiate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_forall.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_instantiate.case_0
  store_step with ih.eo__24is_5finstantiation s1 v7 a0 _ _ hinv1 h64 (hG.rem hrem) h_v7 h_a0 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v6 h_v8 hinv1 s1 v6 v8
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 dropping hinv2 s2
  have h_req_v14 := (show requires_0_eo__24eo_5fprog_5finstantiate s3 v9 v10 v4 v7 a0 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5finstantiate
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v9 v10 with h_v9 h_v10 using hinv3 hG
    req_stuck h_v9 as hq_v9 using hinv3 hG
    store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v10 h_v9 hinv3 s3 v10 v9
    step as ⟨e_v12, he_v12⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s4 e_v12 (by rw [he_v12]; exact empty_args) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v4 h_v7 h_v11 dropping he_v12 hinv4 e_v12 s4
    store_step with ih.eo__24substitute_5fsimul_5frec s5 v11 v4 v7 a0 v12 _ _ _ _ _ hinv5 h64 (hG.rem hrem) h_v11 h_v4 h_v7 h_a0 h_v12 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying dropping h_a0 h_v11 h_v12 h_v4 h_v7 hinv5 s5 v11 v12 v4 v7
    req_done hinv6 hG with h_v13 using hq_v9)
  store_step with h_req_v14 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying dropping h_a0 h_req_v14 h_v10 h_v4 h_v7 h_v9 hinv3 s3 v10 v4 v7 v9
  case_done hinv7 hG with h_v14 in EoCases.__eo_prog_instantiate.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_instantiate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5finstantiate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_instantiate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_instantiate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_instantiate
  unfold EoCases.__eo_prog_instantiate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5finstantiate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5finstantiate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_instantiate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5finstantiate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5finstantiate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5finstantiate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_instantiate.case_0

theorem eo__24eo_5fprog_5finstantiate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5finstantiate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5finstantiate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5finstantiate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_instantiate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5finstantiate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_int_to_bv_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_int_to_bv_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_int_to_bv_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_int_to_bv_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_int_to_bv_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_int_to_bv_elim.case_0
  pat_destruct CtorSpec.eo_int_5fto_5fbv.destruct h_v8 as ⟨v11, x_v11, h_v11⟩ else hinv1 hG in EoCases.__eo_prog_int_to_bv_elim.case_0
  obtain hn_v11 := CtorSpec.eo_int_5fto_5fbv.fields_ne_stuck hinv1 h_v8
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_concat.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v4 h_v5 h_v6 h_v8 he_v12 hinv1 e_v12 s1 v4 v5 v6 v8
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping he_v13 hinv2 e_v13 s2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v13 dropping hinv3 s3
  step as ⟨e_v15, he_v15⟩
  store_step with Store.builtin_spec_list_repeat n ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s4 e_v15 (by rw [he_v15]; rfl) h_v13 h_v14 h_v11 hinv4 h64 (hG.rem hrem) op_not_left_eo__40_40TypedList_2econs as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v13 h_v14 he_v15 hinv4 e_v15 s4 v13 v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_is_z s5 e_v16 (by rw [he_v16]; rfl) h_v11 hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping he_v16 hinv5 e_v16 s5
  have h_ite_v24 := (show if_1_eo__24eo_5fprog_5fint_2dto_2dbv_2delim s6 v16 v11 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24eo_5fprog_5fint_2dto_2dbv_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_v16 with ⟨hx_17, hbv_17⟩ | ⟨hx_17, hbv_17⟩ | ⟨hx_17, hbv_17⟩
    · ite_branch hbv_17
      step as ⟨e_v17, he_v17⟩
      store_step with Store.builtin_spec_is_neg s6 e_v17 (by rw [he_v17]; rfl) h_v11 hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_v16 he_v17 e_v17 v16
      have h_ite_v21 := (show if_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim s7 v17 v11 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_term h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
        · ite_branch hbv_18
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_v17 v17
          ite_done hinv8 hG with (eo_ite_true_rep _ hx_18 h_v18)
        · ite_branch hbv_18
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s7 2#u32 (2) (by scalar_tac) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_v17 v17
          step as ⟨e_v20, he_v20⟩
          store_step with Store.builtin_spec_pow s8 e_v20 (by rw [he_v20]; rfl) h_v19 h_v11 hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_v19 he_v20 e_v20 v19
          ite_done hinv9 hG with (eo_ite_false_rep _ hx_18 h_v20)
        · ite_branch hbv_18
          ite_stuck hinv7 hG with hx_18)
      store_step with h_ite_v21 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_ite_v21 h_v17 v17
      ite_done hinv8 hG with (eo_ite_true_rep _ hx_17 h_v21)
    · ite_branch hbv_17
      step as ⟨e_v22, he_v22⟩
      store_step with CtorSpec.eo_int_2epow2.construct s6 e_v22 (by rw [he_v22]; exact empty_args) hinv6 h64 as ⟨v22, s7, hinv7, h_v22⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_v16 he_v22 e_v22 v16
      store_step with Store.apply_rep s7 v22 v11 _ _ hinv7 h64 h_v22 h_v11 (by ns_tac) (by ns_tac) as ⟨v23, s8, hinv8, h_v23⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_v22 v22
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_17 h_v23)
    · ite_branch hbv_17
      ite_stuck hinv6 hG with hx_17)
  store_step with h_ite_v24 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v15 dropping h_ite_v24 h_v16 hinv6 s6 v16
  store_step with ih.eo__24abconv_5fint_5fto_5fbv_5felim s7 v9 v15 v24 _ _ _ hinv7 h64 (hG.rem hrem) h_v9 h_v15 h_v24 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v15 h_v24 hinv7 s7 v15 v24
  step as ⟨e_v26, he_v26⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s8 e_v26 (by rw [he_v26]; rfl) h_v12 h_v25 hinv8 h64 (hG.rem hrem) op_not_left_eo_concat op_nil_apply_eo_concat as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v12 h_v25 he_v26 hinv8 e_v26 s8 v12 v25
  have h_req_v32 := (show requires_2_eo__24eo_5fprog_5fint_2dto_2dbv_2delim s9 v26 v2 v11 v9 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_2_eo__24eo_5fprog_5fint_2dto_2dbv_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    req_same v26 v2 with h_v26 h_v2 using hinv9 hG
    req_stuck h_v26 as hq_v26 using hinv9 hG
    step as ⟨e_v27, he_v27⟩
    store_step with CtorSpec.eo__3d.construct s9 e_v27 (by rw [he_v27]; exact empty_args) hinv9 h64 as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying h_v2 h_v9 h_v11 dropping h_v26 he_v27 hinv9 e_v27 s9 v26
    step as ⟨e_v28, he_v28⟩
    store_step with CtorSpec.eo_int_5fto_5fbv.construct s10 e_v28 (by rw [he_v28]; rfl) h_v11 hinv10 h64 as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying h_v2 h_v9 h_v27 dropping h_v11 he_v28 hinv10 e_v28 s10 v11
    store_step with Store.apply_rep s11 v28 v9 _ _ hinv11 h64 h_v28 h_v9 (by ns_tac) (by ns_tac) as ⟨v29, s12, hinv12, h_v29⟩ growing hG carrying h_v2 h_v27 dropping h_v28 h_v9 hinv11 s11 v28 v9
    store_step with Store.apply_rep s12 v27 v29 _ _ hinv12 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s13, hinv13, h_v30⟩ growing hG carrying h_v2 dropping h_v27 h_v29 hinv12 s12 v27 v29
    store_step with Store.apply_rep s13 v30 v2 _ _ hinv13 h64 h_v30 h_v2 (by ns_tac) (by ns_tac) as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying dropping h_v2 h_v30 hinv13 s13 v2 v30
    req_done hinv14 hG with h_v31 using hq_v26)
  store_step with h_req_v32 as ⟨v32, s15, hinv15, h_v32⟩ growing hG carrying dropping h_req_v32 h_v11 h_v2 h_v26 h_v9 hinv9 s9 v11 v2 v26 v9
  case_done hinv15 hG with h_v32 in EoCases.__eo_prog_int_to_bv_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11

/-- logos's `__eo_prog_int_to_bv_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fint_2dto_2dbv_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_int_to_bv_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_int_to_bv_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_int_to_bv_elim
  unfold EoCases.__eo_prog_int_to_bv_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_int_to_bv_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fint_2dto_2dbv_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_int_to_bv_elim.case_0

theorem eo__24eo_5fprog_5fint_2dto_2dbv_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fint_2dto_2dbv_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fint_2dto_2dbv_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_int_to_bv_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fint_5ftight_5flb_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fint_5ftight_5flb s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_int_tight_lb.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_int_tight_lb.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fint_5ftight_5flb
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_int_tight_lb.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_int_tight_lb.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_int_tight_lb.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3e.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_int_tight_lb.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  store_step with Store.apply_rep s2 v9 v7 _ _ hinv2 h64 h_v9 h_v7 (by ns_tac) (by ns_tac) as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 dropping h_v7 h_v9 hinv2 s2 v7 v9
  store_step with ih.eo__24least_5fint_5fgt s3 v4 _ hinv3 h64 (hG.rem hrem) h_v4 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v10 dropping h_v4 hinv3 s3 v4
  store_step with Store.apply_mk_rep s4 v10 v11 _ _ hinv4 h64 h_v10 h_v11 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying dropping h_v10 h_v11 hinv4 s4 v10 v11
  case_done hinv5 hG with h_v12 in EoCases.__eo_prog_int_tight_lb.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_int_tight_lb` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fint_5ftight_5flb.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_int_tight_lb x_a0 =
      (firstSome [EoCases.__eo_prog_int_tight_lb.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_int_tight_lb
  unfold EoCases.__eo_prog_int_tight_lb.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fint_5ftight_5flb_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fint_5ftight_5flb s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_int_tight_lb x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fint_5ftight_5flb.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fint_5ftight_5flb
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fint_5ftight_5flb_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_int_tight_lb.case_0

theorem eo__24eo_5fprog_5fint_5ftight_5flb_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fint_5ftight_5flb.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fint_5ftight_5flb
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fint_5ftight_5flb s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_int_tight_lb x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fint_5ftight_5flb_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fint_5ftight_5fub_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fint_5ftight_5fub s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_int_tight_ub.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_int_tight_ub.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fint_5ftight_5fub
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_int_tight_ub.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_int_tight_ub.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_int_tight_ub.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3c.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_int_tight_ub.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  store_step with Store.apply_rep s2 v9 v7 _ _ hinv2 h64 h_v9 h_v7 (by ns_tac) (by ns_tac) as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_v4 dropping h_v7 h_v9 hinv2 s2 v7 v9
  store_step with ih.eo__24greatest_5fint_5flt s3 v4 _ hinv3 h64 (hG.rem hrem) h_v4 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_v10 dropping h_v4 hinv3 s3 v4
  store_step with Store.apply_mk_rep s4 v10 v11 _ _ hinv4 h64 h_v10 h_v11 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying dropping h_v10 h_v11 hinv4 s4 v10 v11
  case_done hinv5 hG with h_v12 in EoCases.__eo_prog_int_tight_ub.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_int_tight_ub` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fint_5ftight_5fub.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_int_tight_ub x_a0 =
      (firstSome [EoCases.__eo_prog_int_tight_ub.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_int_tight_ub
  unfold EoCases.__eo_prog_int_tight_ub.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fint_5ftight_5fub_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fint_5ftight_5fub s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_int_tight_ub x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fint_5ftight_5fub.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fint_5ftight_5fub
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fint_5ftight_5fub_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_int_tight_ub.case_0

theorem eo__24eo_5fprog_5fint_5ftight_5fub_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fint_5ftight_5fub.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fint_5ftight_5fub
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fint_5ftight_5fub s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_int_tight_ub x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fint_5ftight_5fub_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2delse_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2delse_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_else_false.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_else_false.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2delse_2dfalse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v6 dropping h_a0 h_v7 hinv8 s8 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_and.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v6 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v6 h_v8 dropping h_a1 h_v9 hinv10 s10 v9
  store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v6 h_v8 h_v10 dropping hinv11 s11
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v6 h_v8 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_rep s13 v8 v12 _ _ hinv13 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v6 dropping h_v12 h_v8 hinv13 s13 v12 v8
  store_step with Store.apply_rep s14 v6 v13 _ _ hinv14 h64 h_v6 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v6 hinv14 s14 v13 v6
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_ite_else_false.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_else_false` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2delse_2dfalse.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_else_false x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_else_false.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_else_false
  unfold EoCases.__eo_prog_ite_else_false.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2delse_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2delse_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_false x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2delse_2dfalse.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2delse_2dfalse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2delse_2dfalse_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_else_false.case_0

theorem eo__24eo_5fprog_5fite_2delse_2dfalse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2delse_2dfalse.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2delse_2dfalse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2delse_2dfalse s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_else_false x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2delse_2dfalse_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_else_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_else_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_ite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 h_v3 dropping h_a2 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 h_v3 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a3 h_v9 dropping h_a0 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a3 h_v9 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v9 dropping h_a3 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v9 hinv14 s14 v13 v9
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_ite_else_lookahead.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_ite_else_lookahead` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2delse_2dlookahead.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_else_lookahead x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_else_lookahead.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_else_lookahead
  unfold EoCases.__eo_prog_ite_else_lookahead.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2delse_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2delse_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2delse_2dlookahead.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2delse_2dlookahead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_ite_else_lookahead.case_0

theorem eo__24eo_5fprog_5fite_2delse_2dlookahead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2delse_2dlookahead.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2delse_2dlookahead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2delse_2dlookahead s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_else_lookahead x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2delse_2dlookahead_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_else_lookahead_not_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_else_lookahead_not_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_not.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v3 v5 _ _ hinv6 h64 h_v3 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v3 h_v5 hinv6 s6 v3 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v7 dropping h_a1 h_v9 hinv10 s10 v9
  store_step with Store.literal_boolean_spec s11 true hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v7 h_v10 dropping hinv11 s11
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v7 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_rep s13 v7 v12 _ _ hinv13 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying dropping h_v12 h_v7 hinv13 s13 v12 v7
  case_done hinv14 hG with h_v13 in EoCases.__eo_prog_ite_else_lookahead_not_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_else_lookahead_not_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_else_lookahead_not_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_else_lookahead_not_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_else_lookahead_not_self
  unfold EoCases.__eo_prog_ite_else_lookahead_not_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_lookahead_not_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_else_lookahead_not_self.case_0

theorem eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_else_lookahead_not_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_else_lookahead_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_else_lookahead_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v4 hinv5 s5 v0 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ite.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 h_v5 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v5 dropping h_a1 h_v7 hinv8 s8 v7
  store_step with Store.literal_boolean_spec s9 false hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v5 h_v8 dropping hinv9 s9
  store_step with Store.apply_rep s10 v8 v9 _ _ hinv10 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v5 dropping h_v8 h_v9 hinv10 s10 v8 v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying dropping h_v10 h_v5 hinv11 s11 v10 v5
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_ite_else_lookahead_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_else_lookahead_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_else_lookahead_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_else_lookahead_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_else_lookahead_self
  unfold EoCases.__eo_prog_ite_else_lookahead_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_lookahead_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_else_lookahead_self.case_0

theorem eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_else_lookahead_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_else_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_else_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_ite.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 h_v4 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v4 v6 _ _ hinv7 h64 h_v4 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v4 h_v6 hinv7 s7 v4 v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v3 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v8 a3 _ _ hinv9 h64 h_v8 h_a3 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v3 dropping h_a3 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v3 v9 _ _ hinv10 h64 h_v3 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v3 h_v9 hinv10 s10 v3 v9
  store_step with Store.apply_rep s11 v0 v10 _ _ hinv11 h64 h_v0 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v10 hinv11 s11 v0 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 dropping he_v12 hinv12 e_v12 s12
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_v11 dropping h_a0 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v13 a1 _ _ hinv14 h64 h_v13 h_a1 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a2 h_v11 dropping h_a1 h_v13 hinv14 s14 v13
  store_step with Store.apply_rep s15 v14 a2 _ _ hinv15 h64 h_v14 h_a2 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v11 dropping h_a2 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v11 v15 _ _ hinv16 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v11 h_v15 hinv16 s16 v11 v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_ite_else_neg_lookahead.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_ite_else_neg_lookahead` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_else_neg_lookahead x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_else_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_else_neg_lookahead
  unfold EoCases.__eo_prog_ite_else_neg_lookahead.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_neg_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_ite_else_neg_lookahead.case_0

theorem eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_else_neg_lookahead x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2delse_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2delse_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_else_true.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_else_true.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2delse_2dtrue
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v6 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v6 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v6 dropping h_v7 h_v9 hinv10 s10 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_v6 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v6 h_v10 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.literal_boolean_spec s13 false hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v6 h_v10 h_v12 dropping hinv13 s13
  store_step with Store.apply_rep s14 v12 v13 _ _ hinv14 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_v6 h_v10 dropping h_v12 h_v13 hinv14 s14 v12 v13
  store_step with Store.apply_rep s15 v10 v14 _ _ hinv15 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v6 dropping h_v10 h_v14 hinv15 s15 v10 v14
  store_step with Store.apply_rep s16 v6 v15 _ _ hinv16 h64 h_v6 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v15 h_v6 hinv16 s16 v15 v6
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_ite_else_true.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_else_true` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2delse_2dtrue.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_else_true x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_else_true.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_else_true
  unfold EoCases.__eo_prog_ite_else_true.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2delse_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2delse_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_else_true x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2delse_2dtrue.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2delse_2dtrue
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2delse_2dtrue_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_else_true.case_0

theorem eo__24eo_5fprog_5fite_2delse_2dtrue_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2delse_2dtrue.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2delse_2dtrue
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2delse_2dtrue s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_else_true x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2delse_2dtrue_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2deq_2dbranch_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2deq_2dbranch s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_eq_branch.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_eq_branch.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2deq_2dbranch
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a1 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_a1 h_v5 hinv6 s6 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_ite_eq_branch.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_eq_branch` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2deq_2dbranch.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_eq_branch x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_eq_branch.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_eq_branch
  unfold EoCases.__eo_prog_ite_eq_branch.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2deq_2dbranch_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2deq_2dbranch s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_eq_branch x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2deq_2dbranch.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2deq_2dbranch
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2deq_2dbranch_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_eq_branch.case_0

theorem eo__24eo_5fprog_5fite_2deq_2dbranch_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2deq_2dbranch.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2deq_2dbranch
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2deq_2dbranch s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_eq_branch x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2deq_2dbranch_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dexpand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dexpand s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_expand.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_expand.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dexpand
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v4 hinv5 s5 v0 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_and.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v5 dropping he_v6 hinv6 e_v6 s6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v5 h_v6 dropping he_v7 hinv7 e_v7 s7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v5 h_v6 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v5 h_v6 h_v7 dropping h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v5 h_v6 dropping h_v7 h_v9 hinv10 s10 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v5 h_v6 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a2 h_v5 h_v6 h_v10 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.literal_boolean_spec s13 false hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a2 h_v5 h_v6 h_v10 h_v12 dropping hinv13 s13
  store_step with Store.apply_rep s14 v12 v13 _ _ hinv14 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a2 h_v5 h_v6 h_v10 dropping h_v12 h_v13 hinv14 s14 v12 v13
  store_step with Store.apply_rep s15 v10 v14 _ _ hinv15 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a2 h_v5 h_v6 dropping h_v10 h_v14 hinv15 s15 v10 v14
  store_step with Store.apply_rep s16 v6 v15 _ _ hinv16 h64 h_v6 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a2 h_v5 dropping h_v15 h_v6 hinv16 s16 v15 v6
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_and.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a2 h_v5 h_v16 dropping he_v17 hinv17 e_v17 s17
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s18 e_v18 (by rw [he_v18]; exact empty_args) hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a2 h_v5 h_v16 h_v17 dropping he_v18 hinv18 e_v18 s18
  store_step with Store.apply_rep s19 v18 a0 _ _ hinv19 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a2 h_v5 h_v16 h_v17 dropping h_a0 h_v18 hinv19 s19 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s20 e_v20 (by rw [he_v20]; exact empty_args) hinv20 h64 as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a2 h_v5 h_v16 h_v17 h_v19 dropping he_v20 hinv20 e_v20 s20
  store_step with Store.apply_rep s21 v20 a2 _ _ hinv21 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_v5 h_v16 h_v17 h_v19 dropping h_a2 h_v20 hinv21 s21 v20
  store_step with Store.literal_boolean_spec s22 false hinv22 h64 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_v5 h_v16 h_v17 h_v19 h_v21 dropping hinv22 s22
  store_step with Store.apply_rep s23 v21 v22 _ _ hinv23 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_v5 h_v16 h_v17 h_v19 dropping h_v21 h_v22 hinv23 s23 v21 v22
  store_step with Store.apply_rep s24 v19 v23 _ _ hinv24 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_v5 h_v16 h_v17 dropping h_v19 h_v23 hinv24 s24 v19 v23
  store_step with Store.apply_rep s25 v17 v24 _ _ hinv25 h64 h_v17 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_v5 h_v16 dropping h_v17 h_v24 hinv25 s25 v17 v24
  store_step with Store.literal_boolean_spec s26 true hinv26 h64 as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_v5 h_v16 h_v25 dropping hinv26 s26
  store_step with Store.apply_rep s27 v25 v26 _ _ hinv27 h64 h_v25 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_v5 h_v16 dropping h_v25 h_v26 hinv27 s27 v25 v26
  store_step with Store.apply_rep s28 v16 v27 _ _ hinv28 h64 h_v16 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying h_v5 dropping h_v16 h_v27 hinv28 s28 v16 v27
  store_step with Store.apply_rep s29 v5 v28 _ _ hinv29 h64 h_v5 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s30, hinv30, h_v29⟩ growing hG carrying dropping h_v28 h_v5 hinv29 s29 v28 v5
  case_done hinv30 hG with h_v29 in EoCases.__eo_prog_ite_expand.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_ite_expand` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dexpand.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_ite_expand x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_expand.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_expand
  unfold EoCases.__eo_prog_ite_expand.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dexpand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fite_2dexpand s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_expand x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dexpand.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fite_2dexpand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dexpand_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_ite_expand.case_0

theorem eo__24eo_5fprog_5fite_2dexpand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dexpand.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fite_2dexpand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dexpand s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_ite_expand x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dexpand_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_false_cond.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_false_cond.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping hinv2 s2
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v2 hinv3 s3 v1 v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 h_v0 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_a1 h_v6 hinv7 s7 v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_ite_false_cond.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_false_cond` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dfalse_2dcond.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_false_cond x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_false_cond.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_false_cond
  unfold EoCases.__eo_prog_ite_false_cond.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dfalse_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_false_cond x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dfalse_2dcond.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dfalse_2dcond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_false_cond.case_0

theorem eo__24eo_5fprog_5fite_2dfalse_2dcond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dfalse_2dcond.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dfalse_2dcond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dfalse_2dcond s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_false_cond x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dfalse_2dcond_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_neg_branch.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_neg_branch.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_neg_branch.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_not.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  pat_same v4 a1 with h_v4 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_ite_neg_branch.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v10 h_v11 h_v12 h_v4 he_v13 hinv2 e_v13 s2 v10 v11 v12 v4
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping h_v14 hinv4 s4 v14
  store_step with Store.apply_rep s5 v15 a1 _ _ hinv5 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping h_v15 hinv5 s5 v15
  store_step with Store.apply_rep s6 v16 a2 _ _ hinv6 h64 h_v16 h_a2 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_v13 dropping h_a2 h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v13 v17 _ _ hinv7 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 dropping h_v13 h_v17 hinv7 s7 v13 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v19 (by rw [he_v19]; exact empty_args) hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_v18 dropping he_v19 hinv8 e_v19 s8
  store_step with Store.apply_rep s9 v19 a0 _ _ hinv9 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a1 h_v18 dropping h_a0 h_v19 hinv9 s9 v19
  store_step with Store.apply_rep s10 v20 a1 _ _ hinv10 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_v18 dropping h_a1 h_v20 hinv10 s10 v20
  store_step with Store.apply_rep s11 v18 v21 _ _ hinv11 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying dropping h_v18 h_v21 hinv11 s11 v18 v21
  case_done hinv12 hG with h_v22 in EoCases.__eo_prog_ite_neg_branch.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_ite_neg_branch` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dneg_2dbranch.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_neg_branch.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_neg_branch
  unfold EoCases.__eo_prog_ite_neg_branch.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2dneg_2dbranch s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dneg_2dbranch.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2dneg_2dbranch
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_ite_neg_branch.case_0

theorem eo__24eo_5fprog_5fite_2dneg_2dbranch_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dneg_2dbranch.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2dneg_2dbranch
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dneg_2dbranch s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_neg_branch x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dneg_2dbranch_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dnot_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dnot_2dcond s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_not_cond.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_not_cond.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dnot_2dcond
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_not.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 h_v3 hinv4 s4 v1 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_a2 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v9 a2 _ _ hinv10 h64 h_v9 h_a2 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v7 dropping h_a2 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v10 a1 _ _ hinv11 h64 h_v10 h_a1 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v7 dropping h_a1 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v7 v11 _ _ hinv12 h64 h_v7 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying dropping h_v11 h_v7 hinv12 s12 v11 v7
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_ite_not_cond.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_ite_not_cond` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dnot_2dcond.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_ite_not_cond x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_not_cond.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_not_cond
  unfold EoCases.__eo_prog_ite_not_cond.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dnot_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fite_2dnot_2dcond s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_not_cond x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dnot_2dcond.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fite_2dnot_2dcond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dnot_2dcond_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_ite_not_cond.case_0

theorem eo__24eo_5fprog_5fite_2dnot_2dcond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dnot_2dcond.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fite_2dnot_2dcond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dnot_2dcond s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_ite_not_cond x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dnot_2dcond_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_false.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_false.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping hinv3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v6 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v6 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v6 dropping h_v7 h_v9 hinv10 s10 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_and.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_v6 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v6 h_v10 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.literal_boolean_spec s13 true hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v6 h_v10 h_v12 dropping hinv13 s13
  store_step with Store.apply_rep s14 v12 v13 _ _ hinv14 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_v6 h_v10 dropping h_v12 h_v13 hinv14 s14 v12 v13
  store_step with Store.apply_rep s15 v10 v14 _ _ hinv15 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v6 dropping h_v10 h_v14 hinv15 s15 v10 v14
  store_step with Store.apply_rep s16 v6 v15 _ _ hinv16 h64 h_v6 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v15 h_v6 hinv16 s16 v15 v6
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_ite_then_false.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_false` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dfalse.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_false x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_false.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_false
  unfold EoCases.__eo_prog_ite_then_false.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dfalse s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_false x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dfalse.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dfalse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_false.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dfalse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dfalse.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dfalse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dfalse s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_false x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dfalse_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 h_v2 dropping h_a2 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.apply_rep s8 v7 a3 _ _ hinv8 h64 h_v7 h_a3 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v0 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a3 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a3 h_v9 dropping h_a0 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a3 h_v9 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v9 dropping h_a3 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v9 hinv14 s14 v13 v9
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_ite_then_lookahead.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_ite_then_lookahead` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_lookahead.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_lookahead
  unfold EoCases.__eo_prog_ite_then_lookahead.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2dthen_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dlookahead.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dlookahead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_ite_then_lookahead.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dlookahead.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2dthen_2dlookahead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dlookahead s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_lookahead x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v4 hinv5 s5 v2 v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v7 h_v9 dropping hinv10 s10
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_v7 dropping h_v10 h_v9 hinv11 s11 v10 v9
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v7 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v7 v12 _ _ hinv13 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying dropping h_v12 h_v7 hinv13 s13 v12 v7
  case_done hinv14 hG with h_v13 in EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_lookahead_not_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_lookahead_not_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_lookahead_not_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_lookahead_not_self
  unfold EoCases.__eo_prog_ite_then_lookahead_not_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead_not_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_lookahead_not_self.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_lookahead_not_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
