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

theorem case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_implies_neg2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_implies_neg2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_implies_neg2.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_implies_neg2.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_implies_neg2.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d_3e.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v7 dropping h_v5 h_v8 hinv3 s3 v5 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v11 dropping he_v12 hinv6 e_v12 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v11 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v2 _ _ hinv8 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v11 h_v12 dropping h_v13 h_v2 hinv8 s8 v13 v2
  store_step with Store.apply_rep s9 v12 v14 _ _ hinv9 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v11 dropping h_v12 h_v14 hinv9 s9 v12 v14
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v11 h_v15 dropping hinv10 s10
  store_step with Store.apply_rep s11 v15 v16 _ _ hinv11 h64 h_v15 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v11 dropping h_v15 h_v16 hinv11 s11 v15 v16
  store_step with Store.apply_rep s12 v11 v17 _ _ hinv12 h64 h_v11 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying dropping h_v11 h_v17 hinv12 s12 v11 v17
  case_done hinv13 hG with h_v18 in EoCases.__eo_prog_cnf_implies_neg2.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_cnf_implies_neg2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fimplies_5fneg2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_implies_neg2 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_implies_neg2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_implies_neg2
  unfold EoCases.__eo_prog_cnf_implies_neg2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_implies_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fimplies_5fneg2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_implies_neg2.case_0

theorem eo__24eo_5fprog_5fcnf_5fimplies_5fneg2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fimplies_5fneg2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fimplies_5fneg2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_implies_neg2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fimplies_5fneg2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_implies_pos.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_implies_pos.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_implies_pos.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_implies_pos.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_implies_pos.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d_3e.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  store_step with Store.apply_rep s7 v7 v12 _ _ hinv7 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 dropping h_v12 h_v7 hinv7 s7 v12 v7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v13 dropping he_v14 hinv8 e_v14 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_not.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 dropping he_v15 hinv9 e_v15 s9
  store_step with Store.apply_rep s10 v15 v5 _ _ hinv10 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v13 h_v14 dropping h_v15 h_v5 hinv10 s10 v15 v5
  store_step with Store.apply_rep s11 v14 v16 _ _ hinv11 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v13 dropping h_v14 h_v16 hinv11 s11 v14 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v13 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 v2 _ _ hinv13 h64 h_v18 h_v2 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v13 h_v17 dropping h_v18 h_v2 hinv13 s13 v18 v2
  store_step with Store.literal_boolean_spec s14 false hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v13 h_v17 h_v19 dropping hinv14 s14
  store_step with Store.apply_rep s15 v19 v20 _ _ hinv15 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v13 h_v17 dropping h_v19 h_v20 hinv15 s15 v19 v20
  store_step with Store.apply_rep s16 v17 v21 _ _ hinv16 h64 h_v17 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v13 dropping h_v17 h_v21 hinv16 s16 v17 v21
  store_step with Store.apply_rep s17 v13 v22 _ _ hinv17 h64 h_v13 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying dropping h_v13 h_v22 hinv17 s17 v13 v22
  case_done hinv18 hG with h_v23 in EoCases.__eo_prog_cnf_implies_pos.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_cnf_implies_pos` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fimplies_5fpos.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_implies_pos x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_implies_pos.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_implies_pos
  unfold EoCases.__eo_prog_cnf_implies_pos.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_implies_pos x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fimplies_5fpos.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fimplies_5fpos_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_implies_pos.case_0

theorem eo__24eo_5fprog_5fcnf_5fimplies_5fpos_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fimplies_5fpos.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fimplies_5fpos
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_implies_pos x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fimplies_5fpos_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_ite_neg1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_ite_neg1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg1.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg1.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_ite_neg1.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_or.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  store_step with Store.apply_rep s3 v11 v8 _ _ hinv3 h64 h_v11 h_v8 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 hinv3 s3 v11
  store_step with Store.apply_rep s4 v12 v5 _ _ hinv4 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v12 hinv4 s4 v12
  store_step with Store.apply_rep s5 v13 v2 _ _ hinv5 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v5 h_v8 h_v10 dropping h_v13 h_v2 hinv5 s5 v13 v2
  store_step with Store.apply_rep s6 v10 v14 _ _ hinv6 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v5 h_v8 dropping h_v10 h_v14 hinv6 s6 v10 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v5 h_v8 h_v15 dropping he_v16 hinv7 e_v16 s7
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v5 h_v8 h_v15 h_v16 dropping he_v17 hinv8 e_v17 s8
  store_step with Store.apply_rep s9 v17 v8 _ _ hinv9 h64 h_v17 h_v8 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v5 h_v15 h_v16 dropping h_v17 h_v8 hinv9 s9 v17 v8
  store_step with Store.apply_rep s10 v16 v18 _ _ hinv10 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v5 h_v15 dropping h_v16 h_v18 hinv10 s10 v16 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v5 h_v15 h_v19 dropping he_v20 hinv11 e_v20 s11
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_not.construct s12 e_v21 (by rw [he_v21]; exact empty_args) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v5 h_v15 h_v19 h_v20 dropping he_v21 hinv12 e_v21 s12
  store_step with Store.apply_rep s13 v21 v5 _ _ hinv13 h64 h_v21 h_v5 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v15 h_v19 h_v20 dropping h_v21 h_v5 hinv13 s13 v21 v5
  store_step with Store.apply_rep s14 v20 v22 _ _ hinv14 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v15 h_v19 dropping h_v20 h_v22 hinv14 s14 v20 v22
  store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v15 h_v19 h_v23 dropping hinv15 s15
  store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v15 h_v19 dropping h_v23 h_v24 hinv16 s16 v23 v24
  store_step with Store.apply_rep s17 v19 v25 _ _ hinv17 h64 h_v19 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v15 dropping h_v19 h_v25 hinv17 s17 v19 v25
  store_step with Store.apply_rep s18 v15 v26 _ _ hinv18 h64 h_v15 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying dropping h_v15 h_v26 hinv18 s18 v15 v26
  case_done hinv19 hG with h_v27 in EoCases.__eo_prog_cnf_ite_neg1.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_cnf_ite_neg1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fite_5fneg1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_ite_neg1 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_ite_neg1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_ite_neg1
  unfold EoCases.__eo_prog_cnf_ite_neg1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fite_5fneg1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fite_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_neg1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fite_5fneg1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fite_5fneg1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg1_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_ite_neg1.case_0

theorem eo__24eo_5fprog_5fcnf_5fite_5fneg1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fite_5fneg1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fite_5fneg1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fite_5fneg1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_ite_neg1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fite_5fneg1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_ite_neg2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_ite_neg2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg2.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg2.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_ite_neg2.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_or.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  store_step with Store.apply_rep s3 v11 v8 _ _ hinv3 h64 h_v11 h_v8 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 hinv3 s3 v11
  store_step with Store.apply_rep s4 v12 v5 _ _ hinv4 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v8 h_v10 dropping h_v12 h_v5 hinv4 s4 v12 v5
  store_step with Store.apply_rep s5 v13 v2 _ _ hinv5 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v8 h_v10 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_rep s6 v10 v14 _ _ hinv6 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v8 dropping h_v10 h_v14 hinv6 s6 v10 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v8 h_v15 dropping he_v16 hinv7 e_v16 s7
  store_step with Store.apply_rep s8 v16 v8 _ _ hinv8 h64 h_v16 h_v8 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v15 dropping h_v16 h_v8 hinv8 s8 v16 v8
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v15 h_v17 dropping he_v18 hinv9 e_v18 s9
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_not.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v15 h_v17 h_v18 dropping he_v19 hinv10 e_v19 s10
  store_step with Store.apply_rep s11 v19 v2 _ _ hinv11 h64 h_v19 h_v2 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v15 h_v17 h_v18 dropping h_v19 h_v2 hinv11 s11 v19 v2
  store_step with Store.apply_rep s12 v18 v20 _ _ hinv12 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v15 h_v17 dropping h_v18 h_v20 hinv12 s12 v18 v20
  store_step with Store.literal_boolean_spec s13 false hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v15 h_v17 h_v21 dropping hinv13 s13
  store_step with Store.apply_rep s14 v21 v22 _ _ hinv14 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v15 h_v17 dropping h_v21 h_v22 hinv14 s14 v21 v22
  store_step with Store.apply_rep s15 v17 v23 _ _ hinv15 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v15 dropping h_v17 h_v23 hinv15 s15 v17 v23
  store_step with Store.apply_rep s16 v15 v24 _ _ hinv16 h64 h_v15 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying dropping h_v15 h_v24 hinv16 s16 v15 v24
  case_done hinv17 hG with h_v25 in EoCases.__eo_prog_cnf_ite_neg2.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_cnf_ite_neg2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fite_5fneg2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_ite_neg2 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_ite_neg2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_ite_neg2
  unfold EoCases.__eo_prog_cnf_ite_neg2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fite_5fneg2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fite_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fite_5fneg2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fite_5fneg2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg2_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_ite_neg2.case_0

theorem eo__24eo_5fprog_5fcnf_5fite_5fneg2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fite_5fneg2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fite_5fneg2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fite_5fneg2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_ite_neg2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fite_5fneg2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_ite_neg3.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_ite_neg3.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg3.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg3.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_neg3.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_ite_neg3.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_or.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  store_step with Store.apply_rep s3 v11 v8 _ _ hinv3 h64 h_v11 h_v8 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v11 h_v8 hinv3 s3 v11 v8
  store_step with Store.apply_rep s4 v12 v5 _ _ hinv4 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v12 hinv4 s4 v12
  store_step with Store.apply_rep s5 v13 v2 _ _ hinv5 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_rep s6 v10 v14 _ _ hinv6 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v14 hinv6 s6 v10 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v15 dropping he_v16 hinv7 e_v16 s7
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v15 h_v16 dropping he_v17 hinv8 e_v17 s8
  store_step with Store.apply_rep s9 v17 v5 _ _ hinv9 h64 h_v17 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v15 h_v16 dropping h_v17 h_v5 hinv9 s9 v17 v5
  store_step with Store.apply_rep s10 v16 v18 _ _ hinv10 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v15 dropping h_v16 h_v18 hinv10 s10 v16 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v15 h_v19 dropping he_v20 hinv11 e_v20 s11
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_not.construct s12 e_v21 (by rw [he_v21]; exact empty_args) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v15 h_v19 h_v20 dropping he_v21 hinv12 e_v21 s12
  store_step with Store.apply_rep s13 v21 v2 _ _ hinv13 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v15 h_v19 h_v20 dropping h_v2 h_v21 hinv13 s13 v2 v21
  store_step with Store.apply_rep s14 v20 v22 _ _ hinv14 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v15 h_v19 dropping h_v20 h_v22 hinv14 s14 v20 v22
  store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v15 h_v19 h_v23 dropping hinv15 s15
  store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v15 h_v19 dropping h_v23 h_v24 hinv16 s16 v23 v24
  store_step with Store.apply_rep s17 v19 v25 _ _ hinv17 h64 h_v19 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v15 dropping h_v19 h_v25 hinv17 s17 v19 v25
  store_step with Store.apply_rep s18 v15 v26 _ _ hinv18 h64 h_v15 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying dropping h_v15 h_v26 hinv18 s18 v15 v26
  case_done hinv19 hG with h_v27 in EoCases.__eo_prog_cnf_ite_neg3.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_cnf_ite_neg3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fite_5fneg3.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_ite_neg3 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_ite_neg3.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_ite_neg3
  unfold EoCases.__eo_prog_cnf_ite_neg3.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fite_5fneg3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fite_5fneg3 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_neg3 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fite_5fneg3.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fite_5fneg3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fite_5fneg3_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_ite_neg3.case_0

theorem eo__24eo_5fprog_5fcnf_5fite_5fneg3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fite_5fneg3.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fite_5fneg3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fite_5fneg3 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_ite_neg3 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fite_5fneg3_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_ite_pos1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_ite_pos1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos1.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos1.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_ite_pos1.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_or.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_not.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with Store.apply_rep s4 v12 v8 _ _ hinv4 h64 h_v12 h_v8 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v12 hinv4 s4 v12
  store_step with Store.apply_rep s5 v13 v5 _ _ hinv5 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_rep s6 v14 v2 _ _ hinv6 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v5 h_v8 h_v10 h_v11 dropping h_v14 h_v2 hinv6 s6 v14 v2
  store_step with Store.apply_rep s7 v11 v15 _ _ hinv7 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v5 h_v8 h_v10 dropping h_v11 h_v15 hinv7 s7 v11 v15
  store_step with Store.apply_rep s8 v10 v16 _ _ hinv8 h64 h_v10 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v5 h_v8 dropping h_v10 h_v16 hinv8 s8 v10 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v5 h_v8 h_v17 dropping he_v18 hinv9 e_v18 s9
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_not.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v5 h_v8 h_v17 h_v18 dropping he_v19 hinv10 e_v19 s10
  store_step with Store.apply_rep s11 v19 v8 _ _ hinv11 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v5 h_v17 h_v18 dropping h_v19 h_v8 hinv11 s11 v19 v8
  store_step with Store.apply_rep s12 v18 v20 _ _ hinv12 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v5 h_v17 dropping h_v18 h_v20 hinv12 s12 v18 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_or.construct s13 e_v22 (by rw [he_v22]; exact empty_args) hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v5 h_v17 h_v21 dropping he_v22 hinv13 e_v22 s13
  store_step with Store.apply_rep s14 v22 v5 _ _ hinv14 h64 h_v22 h_v5 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v17 h_v21 dropping h_v22 h_v5 hinv14 s14 v22 v5
  store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v17 h_v21 h_v23 dropping hinv15 s15
  store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v17 h_v21 dropping h_v23 h_v24 hinv16 s16 v23 v24
  store_step with Store.apply_rep s17 v21 v25 _ _ hinv17 h64 h_v21 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v17 dropping h_v21 h_v25 hinv17 s17 v21 v25
  store_step with Store.apply_rep s18 v17 v26 _ _ hinv18 h64 h_v17 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying dropping h_v17 h_v26 hinv18 s18 v17 v26
  case_done hinv19 hG with h_v27 in EoCases.__eo_prog_cnf_ite_pos1.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_cnf_ite_pos1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fite_5fpos1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_ite_pos1 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_ite_pos1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_ite_pos1
  unfold EoCases.__eo_prog_cnf_ite_pos1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fite_5fpos1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fite_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_pos1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fite_5fpos1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fite_5fpos1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos1_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_ite_pos1.case_0

theorem eo__24eo_5fprog_5fcnf_5fite_5fpos1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fite_5fpos1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fite_5fpos1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fite_5fpos1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_ite_pos1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fite_5fpos1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_ite_pos2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_ite_pos2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos2.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos2.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_ite_pos2.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_or.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_not.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with Store.apply_rep s4 v12 v8 _ _ hinv4 h64 h_v12 h_v8 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v12 hinv4 s4 v12
  store_step with Store.apply_rep s5 v13 v5 _ _ hinv5 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v8 h_v10 h_v11 dropping h_v13 h_v5 hinv5 s5 v13 v5
  store_step with Store.apply_rep s6 v14 v2 _ _ hinv6 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v8 h_v10 h_v11 dropping h_v14 hinv6 s6 v14
  store_step with Store.apply_rep s7 v11 v15 _ _ hinv7 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v8 h_v10 dropping h_v11 h_v15 hinv7 s7 v11 v15
  store_step with Store.apply_rep s8 v10 v16 _ _ hinv8 h64 h_v10 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v8 dropping h_v10 h_v16 hinv8 s8 v10 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v8 h_v17 dropping he_v18 hinv9 e_v18 s9
  store_step with Store.apply_rep s10 v18 v8 _ _ hinv10 h64 h_v18 h_v8 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v17 dropping h_v18 h_v8 hinv10 s10 v18 v8
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v17 h_v19 dropping he_v20 hinv11 e_v20 s11
  store_step with Store.apply_rep s12 v20 v2 _ _ hinv12 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v17 h_v19 dropping h_v2 h_v20 hinv12 s12 v2 v20
  store_step with Store.literal_boolean_spec s13 false hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v17 h_v19 h_v21 dropping hinv13 s13
  store_step with Store.apply_rep s14 v21 v22 _ _ hinv14 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v22 hinv14 s14 v21 v22
  store_step with Store.apply_rep s15 v19 v23 _ _ hinv15 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v17 dropping h_v19 h_v23 hinv15 s15 v19 v23
  store_step with Store.apply_rep s16 v17 v24 _ _ hinv16 h64 h_v17 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying dropping h_v17 h_v24 hinv16 s16 v17 v24
  case_done hinv17 hG with h_v25 in EoCases.__eo_prog_cnf_ite_pos2.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_cnf_ite_pos2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fite_5fpos2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_ite_pos2 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_ite_pos2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_ite_pos2
  unfold EoCases.__eo_prog_cnf_ite_pos2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fite_5fpos2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fite_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_pos2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fite_5fpos2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fite_5fpos2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos2_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_ite_pos2.case_0

theorem eo__24eo_5fprog_5fcnf_5fite_5fpos2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fite_5fpos2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fite_5fpos2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fite_5fpos2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_ite_pos2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fite_5fpos2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_ite_pos3.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_ite_pos3.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos3.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos3.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_ite_pos3.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_ite_pos3.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_or.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_not.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with Store.apply_rep s4 v12 v8 _ _ hinv4 h64 h_v12 h_v8 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v10 h_v11 dropping h_v12 h_v8 hinv4 s4 v12 v8
  store_step with Store.apply_rep s5 v13 v5 _ _ hinv5 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v10 h_v11 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_rep s6 v14 v2 _ _ hinv6 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v10 h_v11 dropping h_v14 hinv6 s6 v14
  store_step with Store.apply_rep s7 v11 v15 _ _ hinv7 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v10 dropping h_v11 h_v15 hinv7 s7 v11 v15
  store_step with Store.apply_rep s8 v10 v16 _ _ hinv8 h64 h_v10 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v16 hinv8 s8 v10 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v17 dropping he_v18 hinv9 e_v18 s9
  store_step with Store.apply_rep s10 v18 v5 _ _ hinv10 h64 h_v18 h_v5 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v17 dropping h_v18 h_v5 hinv10 s10 v18 v5
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v17 h_v19 dropping he_v20 hinv11 e_v20 s11
  store_step with Store.apply_rep s12 v20 v2 _ _ hinv12 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v17 h_v19 dropping h_v2 h_v20 hinv12 s12 v2 v20
  store_step with Store.literal_boolean_spec s13 false hinv13 h64 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v17 h_v19 h_v21 dropping hinv13 s13
  store_step with Store.apply_rep s14 v21 v22 _ _ hinv14 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v17 h_v19 dropping h_v21 h_v22 hinv14 s14 v21 v22
  store_step with Store.apply_rep s15 v19 v23 _ _ hinv15 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v17 dropping h_v19 h_v23 hinv15 s15 v19 v23
  store_step with Store.apply_rep s16 v17 v24 _ _ hinv16 h64 h_v17 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying dropping h_v17 h_v24 hinv16 s16 v17 v24
  case_done hinv17 hG with h_v25 in EoCases.__eo_prog_cnf_ite_pos3.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_cnf_ite_pos3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fite_5fpos3.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_ite_pos3 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_ite_pos3.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_ite_pos3
  unfold EoCases.__eo_prog_cnf_ite_pos3.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fite_5fpos3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fite_5fpos3 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_ite_pos3 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fite_5fpos3.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fite_5fpos3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fite_5fpos3_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_ite_pos3.case_0

theorem eo__24eo_5fprog_5fcnf_5fite_5fpos3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fite_5fpos3.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fite_5fpos3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fite_5fpos3 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_ite_pos3 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fite_5fpos3_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5for_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5for_5fneg s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_or_neg.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_or_neg.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5for_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 dropping h_v0 hinv1 s1 v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_or.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v1 dropping he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 dropping he_v3 hinv3 e_v3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_or.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 dropping he_v4 hinv4 e_v4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s5 e_v5 (by rw [he_v5]; rfl) h_v4 h_a0 h_a1 hinv5 h64 (hG.rem hrem) op_not_left_eo_or as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v1 h_v2 h_v3 dropping h_a0 h_a1 h_v4 he_v5 hinv5 e_v5 s5 v4
  store_step with Store.apply_mk_rep s6 v3 v5 _ _ hinv6 h64 h_v3 h_v5 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v1 h_v2 dropping h_v3 h_v5 hinv6 s6 v3 v5
  store_step with Store.apply_mk_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v1 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v1 h_v7 dropping hinv8 s8
  store_step with Store.apply_mk_rep s9 v7 v8 _ _ hinv9 h64 h_v7 h_v8 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v1 dropping h_v7 h_v8 hinv9 s9 v7 v8
  store_step with Store.apply_mk_rep s10 v1 v9 _ _ hinv10 h64 h_v1 h_v9 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_v1 h_v9 hinv10 s10 v1 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_cnf_or_neg.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_cnf_or_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5for_5fneg.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_cnf_or_neg x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_or_neg.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_or_neg
  unfold EoCases.__eo_prog_cnf_or_neg.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5for_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fcnf_5for_5fneg s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_or_neg x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5for_5fneg.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fcnf_5for_5fneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5for_5fneg_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_cnf_or_neg.case_0

theorem eo__24eo_5fprog_5fcnf_5for_5fneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5for_5fneg.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fcnf_5for_5fneg
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5for_5fneg s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_cnf_or_neg x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5for_5fneg_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5for_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5for_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_or_pos.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_or_pos.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5for_5fpos
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_not.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v0 v2 _ _ hinv3 h64 h_v0 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 dropping h_v0 h_v2 hinv3 s3 v0 v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a0 h_v3 hinv4 s4 v3
  case_done hinv5 hG with h_v4 in EoCases.__eo_prog_cnf_or_pos.case_0 using hn_a0

/-- logos's `__eo_prog_cnf_or_pos` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5for_5fpos.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_or_pos x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_or_pos.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_or_pos
  unfold EoCases.__eo_prog_cnf_or_pos.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5for_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5for_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_or_pos x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5for_5fpos.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5for_5fpos
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5for_5fpos_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_or_pos.case_0

theorem eo__24eo_5fprog_5fcnf_5for_5fpos_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5for_5fpos.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5for_5fpos
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5for_5fpos s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_or_pos x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5for_5fpos_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_xor_neg1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_xor_neg1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_neg1.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_neg1.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_xor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_xor_neg1.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_xor.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v5 _ _ hinv8 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v11 h_v12 dropping h_v13 h_v5 hinv8 s8 v13 v5
  store_step with Store.apply_rep s9 v12 v14 _ _ hinv9 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v11 dropping h_v12 h_v14 hinv9 s9 v12 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v11 h_v15 dropping he_v16 hinv10 e_v16 s10
  store_step with Store.apply_rep s11 v16 v2 _ _ hinv11 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v11 h_v15 dropping h_v16 h_v2 hinv11 s11 v16 v2
  store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v11 h_v15 h_v17 dropping hinv12 s12
  store_step with Store.apply_rep s13 v17 v18 _ _ hinv13 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v11 h_v15 dropping h_v17 h_v18 hinv13 s13 v17 v18
  store_step with Store.apply_rep s14 v15 v19 _ _ hinv14 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v11 dropping h_v15 h_v19 hinv14 s14 v15 v19
  store_step with Store.apply_rep s15 v11 v20 _ _ hinv15 h64 h_v11 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying dropping h_v11 h_v20 hinv15 s15 v11 v20
  case_done hinv16 hG with h_v21 in EoCases.__eo_prog_cnf_xor_neg1.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_cnf_xor_neg1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fxor_5fneg1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_xor_neg1 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_xor_neg1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_xor_neg1
  unfold EoCases.__eo_prog_cnf_xor_neg1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_neg1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fxor_5fneg1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg1_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_xor_neg1.case_0

theorem eo__24eo_5fprog_5fcnf_5fxor_5fneg1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fxor_5fneg1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fxor_5fneg1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_xor_neg1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fxor_5fneg1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_xor_neg2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_xor_neg2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_neg2.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_neg2.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_xor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_xor_neg2.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_xor.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
  store_step with Store.apply_rep s7 v12 v5 _ _ hinv7 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v11 dropping h_v12 h_v5 hinv7 s7 v12 v5
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v11 h_v13 dropping he_v14 hinv8 e_v14 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_not.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v11 h_v13 h_v14 dropping he_v15 hinv9 e_v15 s9
  store_step with Store.apply_rep s10 v15 v2 _ _ hinv10 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v11 h_v13 h_v14 dropping h_v15 h_v2 hinv10 s10 v15 v2
  store_step with Store.apply_rep s11 v14 v16 _ _ hinv11 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v11 h_v13 dropping h_v14 h_v16 hinv11 s11 v14 v16
  store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v11 h_v13 h_v17 dropping hinv12 s12
  store_step with Store.apply_rep s13 v17 v18 _ _ hinv13 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v11 h_v13 dropping h_v17 h_v18 hinv13 s13 v17 v18
  store_step with Store.apply_rep s14 v13 v19 _ _ hinv14 h64 h_v13 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v11 dropping h_v13 h_v19 hinv14 s14 v13 v19
  store_step with Store.apply_rep s15 v11 v20 _ _ hinv15 h64 h_v11 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying dropping h_v11 h_v20 hinv15 s15 v11 v20
  case_done hinv16 hG with h_v21 in EoCases.__eo_prog_cnf_xor_neg2.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_cnf_xor_neg2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fxor_5fneg2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_xor_neg2 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_xor_neg2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_xor_neg2
  unfold EoCases.__eo_prog_cnf_xor_neg2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_neg2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fxor_5fneg2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fxor_5fneg2_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_xor_neg2.case_0

theorem eo__24eo_5fprog_5fcnf_5fxor_5fneg2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fxor_5fneg2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fxor_5fneg2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_xor_neg2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fxor_5fneg2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_xor_pos1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_xor_pos1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_pos1.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_pos1.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_xor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_xor_pos1.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_xor.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  store_step with Store.apply_rep s7 v7 v12 _ _ hinv7 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 dropping h_v12 h_v7 hinv7 s7 v12 v7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v13 dropping he_v14 hinv8 e_v14 s8
  store_step with Store.apply_rep s9 v14 v5 _ _ hinv9 h64 h_v14 h_v5 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v13 dropping h_v14 h_v5 hinv9 s9 v14 v5
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v13 h_v15 dropping he_v16 hinv10 e_v16 s10
  store_step with Store.apply_rep s11 v16 v2 _ _ hinv11 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v13 h_v15 dropping h_v16 h_v2 hinv11 s11 v16 v2
  store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v13 h_v15 h_v17 dropping hinv12 s12
  store_step with Store.apply_rep s13 v17 v18 _ _ hinv13 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v13 h_v15 dropping h_v17 h_v18 hinv13 s13 v17 v18
  store_step with Store.apply_rep s14 v15 v19 _ _ hinv14 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v13 dropping h_v15 h_v19 hinv14 s14 v15 v19
  store_step with Store.apply_rep s15 v13 v20 _ _ hinv15 h64 h_v13 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying dropping h_v13 h_v20 hinv15 s15 v13 v20
  case_done hinv16 hG with h_v21 in EoCases.__eo_prog_cnf_xor_pos1.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_cnf_xor_pos1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fxor_5fpos1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_xor_pos1 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_xor_pos1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_xor_pos1
  unfold EoCases.__eo_prog_cnf_xor_pos1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_pos1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fxor_5fpos1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos1_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_xor_pos1.case_0

theorem eo__24eo_5fprog_5fcnf_5fxor_5fpos1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fxor_5fpos1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fxor_5fpos1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_xor_pos1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fxor_5fpos1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_cnf_xor_pos2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_cnf_xor_pos2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_pos2.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_cnf_xor_pos2.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_xor.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_cnf_xor_pos2.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_xor.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  store_step with Store.apply_rep s7 v7 v12 _ _ hinv7 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 dropping h_v12 h_v7 hinv7 s7 v12 v7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v13 dropping he_v14 hinv8 e_v14 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_not.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 dropping he_v15 hinv9 e_v15 s9
  store_step with Store.apply_rep s10 v15 v5 _ _ hinv10 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v13 h_v14 dropping h_v15 h_v5 hinv10 s10 v15 v5
  store_step with Store.apply_rep s11 v14 v16 _ _ hinv11 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v13 dropping h_v14 h_v16 hinv11 s11 v14 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v13 h_v17 dropping he_v18 hinv12 e_v18 s12
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_not.construct s13 e_v19 (by rw [he_v19]; exact empty_args) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v13 h_v17 h_v18 dropping he_v19 hinv13 e_v19 s13
  store_step with Store.apply_rep s14 v19 v2 _ _ hinv14 h64 h_v19 h_v2 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v13 h_v17 h_v18 dropping h_v19 h_v2 hinv14 s14 v19 v2
  store_step with Store.apply_rep s15 v18 v20 _ _ hinv15 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v13 h_v17 dropping h_v18 h_v20 hinv15 s15 v18 v20
  store_step with Store.literal_boolean_spec s16 false hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v13 h_v17 h_v21 dropping hinv16 s16
  store_step with Store.apply_rep s17 v21 v22 _ _ hinv17 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v13 h_v17 dropping h_v21 h_v22 hinv17 s17 v21 v22
  store_step with Store.apply_rep s18 v17 v23 _ _ hinv18 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v13 dropping h_v17 h_v23 hinv18 s18 v17 v23
  store_step with Store.apply_rep s19 v13 v24 _ _ hinv19 h64 h_v13 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying dropping h_v13 h_v24 hinv19 s19 v13 v24
  case_done hinv20 hG with h_v25 in EoCases.__eo_prog_cnf_xor_pos2.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__eo_prog_cnf_xor_pos2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fcnf_5fxor_5fpos2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_cnf_xor_pos2 x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_cnf_xor_pos2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_cnf_xor_pos2
  unfold EoCases.__eo_prog_cnf_xor_pos2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_cnf_xor_pos2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fcnf_5fxor_5fpos2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fcnf_5fxor_5fpos2_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_cnf_xor_pos2.case_0

theorem eo__24eo_5fprog_5fcnf_5fxor_5fpos2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fcnf_5fxor_5fpos2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fcnf_5fxor_5fpos2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_cnf_xor_pos2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fcnf_5fxor_5fpos2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

set_option maxHeartbeats 3660000 in
theorem case_0_eo__24eo_5fprog_5fconcat_5fcsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5fcsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_csplit.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_csplit.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5fcsplit
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a2 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v10, x_v10, h_v10⟩ else hinv1 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v10 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s1 e_v14 (by rw [he_v14]; exact empty_args) hinv1 h64 as ⟨v14, s2, hinv2, h_v14⟩ growing hG carrying h_a0 h_v4 h_v7 h_v12 h_v13 dropping h_a2 h_v10 h_v6 h_v8 he_v14 hinv1 e_v14 s1 v10 v6 v8
  pat_same v12 v14 with h_v12 h_v14 using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_v4 h_v7 h_v17 h_v19 h_v20 dropping h_v12 h_v13 h_v14 h_v16 he_v21 hinv2 e_v21 s2 v12 v13 v14 v16
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_csplit.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_v4 h_v7 h_v17 h_v23 h_v24 dropping h_v19 h_v20 h_v21 he_v25 hinv3 e_v25 s3 v19 v20 v21
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_concat_csplit.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_v4 h_v7 h_v17 h_v24 dropping h_v23 h_v25 hinv4 s4 v23 v25
  pat_same v17 v26 with h_v17 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_concat_csplit.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 dropping h_v17 h_v26 he_v27 hinv5 e_v27 s5 v17 v26
  have h_ite_v34 := (show if_0_eo__24eo_5fprog_5fconcat_5fcsplit s6 a0 v7 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fconcat_5fcsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_a0 with ⟨hx_28, hbv_28⟩ | ⟨hx_28, hbv_28⟩ | ⟨hx_28, hbv_28⟩
    · ite_branch hbv_28
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v27 dropping he_v28 e_v28
      step as ⟨e_v29, he_v29⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v29 (by rw [he_v29]; exact empty_args) hinv7 h64 as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v27 h_v28 dropping he_v29 e_v29
      step as ⟨e_v30, he_v30⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s8 e_v30 (by rw [he_v30]; rfl) h_v29 h_v7 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v27 h_v28 dropping h_v29 he_v30 e_v30 v29
      step as ⟨e_v31, he_v31⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s9 e_v31 (by rw [he_v31]; rfl) h_v28 h_v30 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v27 dropping h_v28 h_v30 he_v31 e_v31 v28 v30
      ite_done hinv10 hG with (eo_ite_true_rep _ hx_28 h_v31)
    · ite_branch hbv_28
      step as ⟨e_v32, he_v32⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v32 (by rw [he_v32]; exact empty_args) hinv6 h64 as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v27 dropping he_v32 e_v32
      step as ⟨e_v33, he_v33⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v33 (by rw [he_v33]; rfl) h_v32 h_v7 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v33, s8, hinv8, h_v33⟩ growing hG carrying h_a0 h_v4 h_v24 h_v27 dropping h_v32 h_v7 he_v33 e_v33 v32 v7
      ite_done hinv8 hG with (eo_ite_false_rep _ hx_28 h_v33)
    · ite_branch hbv_28
      ite_stuck hinv6 hG with hx_28)
  store_step with h_ite_v34 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_v4 h_v24 h_v27 dropping h_ite_v34 h_v7 hinv6 s6 v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_v4 h_v24 h_v27 h_v34 dropping hinv7 s7
  step as ⟨e_v36, he_v36⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s8 e_v36 (by rw [he_v36]; rfl) h_v27 h_v34 h_v35 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v27 h_v34 h_v35 he_v36 hinv8 e_v36 s8 v27 v34 v35
  have h_req_v143 := (show requires_12_eo__24eo_5fprog_5fconcat_5fcsplit s9 v36 v24 a0 v4 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_12_eo__24eo_5fprog_5fconcat_5fcsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    req_same v36 v24 with h_v36 h_v24 using hinv9 hG
    req_stuck h_v36 as hq_v36 using hinv9 hG
    step as ⟨e_v37, he_v37⟩
    store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v36 he_v37 hinv9 e_v37 s9 v36
    have h_ite_v44 := (show if_1_eo__24eo_5fprog_5fconcat_5fcsplit s10 a0 v4 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_1_eo__24eo_5fprog_5fconcat_5fcsplit
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s10
      rcases Store.boolean_value_term h_a0 with ⟨hx_38, hbv_38⟩ | ⟨hx_38, hbv_38⟩ | ⟨hx_38, hbv_38⟩
      · ite_branch hbv_38
        step as ⟨e_v38, he_v38⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v38 (by rw [he_v38]; exact empty_args) hinv10 h64 as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 dropping he_v38 e_v38
        step as ⟨e_v39, he_v39⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s11 e_v39 (by rw [he_v39]; exact empty_args) hinv11 h64 as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 h_v38 dropping he_v39 e_v39
        step as ⟨e_v40, he_v40⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s12 e_v40 (by rw [he_v40]; rfl) h_v39 h_v4 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 h_v38 dropping h_v39 he_v40 e_v40 v39
        step as ⟨e_v41, he_v41⟩
        store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s13 e_v41 (by rw [he_v41]; rfl) h_v38 h_v40 hinv13 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 dropping h_v38 h_v40 he_v41 e_v41 v38 v40
        ite_done hinv14 hG with (eo_ite_true_rep _ hx_38 h_v41)
      · ite_branch hbv_38
        step as ⟨e_v42, he_v42⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v42 (by rw [he_v42]; exact empty_args) hinv10 h64 as ⟨v42, s11, hinv11, h_v42⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 dropping he_v42 e_v42
        step as ⟨e_v43, he_v43⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v43 (by rw [he_v43]; rfl) h_v42 h_v4 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v43, s12, hinv12, h_v43⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 dropping h_v42 he_v43 e_v43 v42
        ite_done hinv12 hG with (eo_ite_false_rep _ hx_38 h_v43)
      · ite_branch hbv_38
        ite_stuck hinv10 hG with hx_38)
    store_step with h_ite_v44 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 dropping h_ite_v44 hinv10 s10
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_v4 h_v24 h_v37 h_v44 dropping hinv11 s11
    step as ⟨e_v46, he_v46⟩
    store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s12 e_v46 (by rw [he_v46]; rfl) h_v37 h_v44 h_v45 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v37 h_v44 h_v45 he_v46 hinv12 e_v46 s12 v37 v44 v45
    step as ⟨e_v47, he_v47⟩
    store_step with Store.builtin_spec_len s13 e_v47 (by rw [he_v47]; rfl) h_v46 hinv13 h64 as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v46 he_v47 hinv13 e_v47 s13 v46
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_v4 h_v24 h_v47 dropping hinv14 s14
    step as ⟨e_v49, he_v49⟩
    store_step with Store.builtin_spec_is_eq s15 e_v49 (by rw [he_v49]; rfl) h_v47 h_v48 hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v47 h_v48 he_v49 hinv15 e_v49 s15 v47 v48
    store_step with Store.literal_boolean_spec s16 true hinv16 h64 as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_v4 h_v24 h_v49 dropping hinv16 s16
    have h_req_v142 := (show requires_11_eo__24eo_5fprog_5fconcat_5fcsplit s17 v49 v50 v24 a0 v4 ⦃ r s' => s'.Inv ∧ s17.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_11_eo__24eo_5fprog_5fconcat_5fcsplit
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s17
      req_same v49 v50 with h_v49 h_v50 using hinv17 hG
      req_stuck h_v49 as hq_v49 using hinv17 hG
      step as ⟨e_v51, he_v51⟩
      store_step with CtorSpec.eo__3d.construct s17 e_v51 (by rw [he_v51]; exact empty_args) hinv17 h64 as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v49 h_v50 he_v51 hinv17 e_v51 s17 v49 v50
      store_step with Store.apply_rep s18 v51 v24 _ _ hinv18 h64 h_v51 h_v24 (by ns_tac) (by ns_tac) as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_v4 h_v24 dropping h_v51 hinv18 s18 v51
      have h_ite_v140 := (show if_10_eo__24eo_5fprog_5fconcat_5fcsplit s19 a0 v24 a0 v4 ⦃ r s' => s'.Inv ∧ s19.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_10_eo__24eo_5fprog_5fconcat_5fcsplit
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s19
        rcases Store.boolean_value_term h_a0 with ⟨hx_53, hbv_53⟩ | ⟨hx_53, hbv_53⟩ | ⟨hx_53, hbv_53⟩
        · ite_branch hbv_53
          step as ⟨e_v53, he_v53⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v53 (by rw [he_v53]; exact empty_args) hinv19 h64 as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 dropping he_v53 e_v53
          step as ⟨e_v54, he_v54⟩
          store_step with CtorSpec.eo__40purify.construct s20 e_v54 (by rw [he_v54]; exact empty_args) hinv20 h64 as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 dropping he_v54 e_v54
          step as ⟨e_v55, he_v55⟩
          store_step with CtorSpec.eo_str_2esubstr.construct s21 e_v55 (by rw [he_v55]; exact empty_args) hinv21 h64 as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 dropping he_v55 e_v55
          store_step with Store.apply_rep s22 v55 v24 _ _ hinv22 h64 h_v55 h_v24 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 dropping h_v55 v55
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s23 0#u32 (0) (by scalar_tac) hinv23 h64 as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v56 dropping
          store_step with Store.apply_rep s24 v56 v57 _ _ hinv24 h64 h_v56 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s25, hinv25, h_v58⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 dropping h_v56 h_v57 v56 v57
          step as ⟨e_v59, he_v59⟩
          store_step with CtorSpec.eo__2d.construct s25 e_v59 (by rw [he_v59]; exact empty_args) hinv25 h64 as ⟨v59, s26, hinv26, h_v59⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v58 dropping he_v59 e_v59
          step as ⟨e_v60, he_v60⟩
          store_step with CtorSpec.eo_str_2elen.construct s26 e_v60 (by rw [he_v60]; exact empty_args) hinv26 h64 as ⟨v60, s27, hinv27, h_v60⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v58 h_v59 dropping he_v60 e_v60
          store_step with Store.apply_rep s27 v60 v24 _ _ hinv27 h64 h_v60 h_v24 (by ns_tac) (by ns_tac) as ⟨v61, s28, hinv28, h_v61⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v58 h_v59 dropping h_v60 v60
          store_step with Store.apply_rep s28 v59 v61 _ _ hinv28 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s29, hinv29, h_v62⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v58 dropping h_v59 h_v61 v59 v61
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v63, s30, hinv30, h_v63⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v58 h_v62 dropping
          store_step with Store.apply_rep s30 v62 v63 _ _ hinv30 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s31, hinv31, h_v64⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 h_v58 dropping h_v62 h_v63 v62 v63
          store_step with Store.apply_rep s31 v58 v64 _ _ hinv31 h64 h_v58 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s32, hinv32, h_v65⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 h_v54 dropping h_v58 h_v64 v58 v64
          store_step with Store.apply_rep s32 v54 v65 _ _ hinv32 h64 h_v54 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s33, hinv33, h_v66⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v53 dropping h_v54 h_v65 v54 v65
          store_step with Store.apply_rep s33 v53 v66 _ _ hinv33 h64 h_v53 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s34, hinv34, h_v67⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 dropping h_v53 h_v66 v53 v66
          step as ⟨e_v68, he_v68⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v68 (by rw [he_v68]; exact empty_args) hinv34 h64 as ⟨v68, s35, hinv35, h_v68⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 dropping he_v68 e_v68
          step as ⟨e_v69, he_v69⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v69 (by rw [he_v69]; exact empty_args) hinv35 h64 as ⟨v69, s36, hinv36, h_v69⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 dropping he_v69 e_v69
          have h_ite_v76 := (show if_2_eo__24eo_5fprog_5fconcat_5fcsplit s36 a0 v4 ⦃ r s' => s'.Inv ∧ s36.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_2_eo__24eo_5fprog_5fconcat_5fcsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s36
            rcases Store.boolean_value_term h_a0 with ⟨hx_70, hbv_70⟩ | ⟨hx_70, hbv_70⟩ | ⟨hx_70, hbv_70⟩
            · ite_branch hbv_70
              step as ⟨e_v70, he_v70⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s36 e_v70 (by rw [he_v70]; exact empty_args) hinv36 h64 as ⟨v70, s37, hinv37, h_v70⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 dropping he_v70 e_v70
              step as ⟨e_v71, he_v71⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s37 e_v71 (by rw [he_v71]; exact empty_args) hinv37 h64 as ⟨v71, s38, hinv38, h_v71⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 h_v70 dropping he_v71 e_v71
              step as ⟨e_v72, he_v72⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s38 e_v72 (by rw [he_v72]; rfl) h_v71 h_v4 hinv38 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v72, s39, hinv39, h_v72⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 h_v70 dropping h_v71 he_v72 e_v72 v71
              step as ⟨e_v73, he_v73⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s39 e_v73 (by rw [he_v73]; rfl) h_v70 h_v72 hinv39 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v73, s40, hinv40, h_v73⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 dropping h_v70 h_v72 he_v73 e_v73 v70 v72
              ite_done hinv40 hG with (eo_ite_true_rep _ hx_70 h_v73)
            · ite_branch hbv_70
              step as ⟨e_v74, he_v74⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s36 e_v74 (by rw [he_v74]; exact empty_args) hinv36 h64 as ⟨v74, s37, hinv37, h_v74⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 dropping he_v74 e_v74
              step as ⟨e_v75, he_v75⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s37 e_v75 (by rw [he_v75]; rfl) h_v74 h_v4 hinv37 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v75, s38, hinv38, h_v75⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 dropping h_v74 he_v75 e_v75 v74
              ite_done hinv38 hG with (eo_ite_false_rep _ hx_70 h_v75)
            · ite_branch hbv_70
              ite_stuck hinv36 hG with hx_70)
          store_step with h_ite_v76 as ⟨v76, s37, hinv37, h_v76⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 dropping h_ite_v76
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s37 0#u32 (0) (by scalar_tac) hinv37 h64 as ⟨v77, s38, hinv38, h_v77⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 h_v69 h_v76 dropping
          step as ⟨e_v78, he_v78⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s38 e_v78 (by rw [he_v78]; rfl) h_v69 h_v76 h_v77 hinv38 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v78, s39, hinv39, h_v78⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v68 dropping h_v69 h_v76 h_v77 he_v78 e_v78 v69 v76 v77
          store_step with Store.apply_mk_rep s39 v68 v78 _ _ hinv39 h64 h_v68 h_v78 as ⟨v79, s40, hinv40, h_v79⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 dropping h_v68 h_v78 v68 v78
          step as ⟨e_v80, he_v80⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v80 (by rw [he_v80]; exact empty_args) hinv40 h64 as ⟨v80, s41, hinv41, h_v80⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 dropping he_v80 e_v80
          step as ⟨e_v81, he_v81⟩
          store_step with CtorSpec.eo__40purify.construct s41 e_v81 (by rw [he_v81]; exact empty_args) hinv41 h64 as ⟨v81, s42, hinv42, h_v81⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 dropping he_v81 e_v81
          step as ⟨e_v82, he_v82⟩
          store_step with CtorSpec.eo_str_2esubstr.construct s42 e_v82 (by rw [he_v82]; exact empty_args) hinv42 h64 as ⟨v82, s43, hinv43, h_v82⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 dropping he_v82 e_v82
          store_step with Store.apply_rep s43 v82 v24 _ _ hinv43 h64 h_v82 h_v24 (by ns_tac) (by ns_tac) as ⟨v83, s44, hinv44, h_v83⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 dropping h_v82 v82
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v84, s45, hinv45, h_v84⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v83 dropping
          store_step with Store.apply_rep s45 v83 v84 _ _ hinv45 h64 h_v83 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s46, hinv46, h_v85⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 dropping h_v83 h_v84 v83 v84
          step as ⟨e_v86, he_v86⟩
          store_step with CtorSpec.eo__2d.construct s46 e_v86 (by rw [he_v86]; exact empty_args) hinv46 h64 as ⟨v86, s47, hinv47, h_v86⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v85 dropping he_v86 e_v86
          step as ⟨e_v87, he_v87⟩
          store_step with CtorSpec.eo_str_2elen.construct s47 e_v87 (by rw [he_v87]; exact empty_args) hinv47 h64 as ⟨v87, s48, hinv48, h_v87⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v85 h_v86 dropping he_v87 e_v87
          store_step with Store.apply_rep s48 v87 v24 _ _ hinv48 h64 h_v87 h_v24 (by ns_tac) (by ns_tac) as ⟨v88, s49, hinv49, h_v88⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v85 h_v86 dropping h_v87 v87
          store_step with Store.apply_rep s49 v86 v88 _ _ hinv49 h64 h_v86 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s50, hinv50, h_v89⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v85 dropping h_v86 h_v88 v86 v88
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s50 1#u32 (1) (by scalar_tac) hinv50 h64 as ⟨v90, s51, hinv51, h_v90⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v85 h_v89 dropping hinv50 s50
          store_step with Store.apply_rep s51 v89 v90 _ _ hinv51 h64 h_v89 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s52, hinv52, h_v91⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 h_v85 dropping h_v89 h_v90 hinv51 s51 v89 v90
          store_step with Store.apply_rep s52 v85 v91 _ _ hinv52 h64 h_v85 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s53, hinv53, h_v92⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 h_v81 dropping h_v85 h_v91 hinv52 s52 v85 v91
          store_step with Store.apply_rep s53 v81 v92 _ _ hinv53 h64 h_v81 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s54, hinv54, h_v93⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 dropping h_v81 h_v92 hinv53 s53 v81 v92
          store_step with ih.eo__24eo_5ftypeof s54 v93 _ hinv54 h64 (hG.rem hrem) h_v93 as ⟨v94, s55, hinv55, h_v94⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 h_v80 dropping h_v93 hinv54 s54 v93
          store_step with ih.eo__24eo_5fnil s55 v80 v94 _ _ hinv55 h64 (hG.rem hrem) h_v80 h_v94 as ⟨v95, s56, hinv56, h_v95⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 h_v79 dropping h_v80 h_v94 hinv55 s55 v80 v94
          store_step with Store.apply_mk_rep s56 v79 v95 _ _ hinv56 h64 h_v79 h_v95 as ⟨v96, s57, hinv57, h_v96⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v67 dropping h_v79 h_v95 hinv56 s56 v79 v95
          store_step with Store.apply_mk_rep s57 v67 v96 _ _ hinv57 h64 h_v67 h_v96 as ⟨v97, s58, hinv58, h_v97⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 dropping h_v67 h_v96 hinv57 s57 v67 v96
          ite_done hinv58 hG with (eo_ite_true_rep _ hx_53 h_v97)
        · ite_branch hbv_53
          step as ⟨e_v98, he_v98⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v98 (by rw [he_v98]; exact empty_args) hinv19 h64 as ⟨v98, s20, hinv20, h_v98⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 dropping he_v98 e_v98
          step as ⟨e_v99, he_v99⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s20 e_v99 (by rw [he_v99]; exact empty_args) hinv20 h64 as ⟨v99, s21, hinv21, h_v99⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 dropping he_v99 e_v99
          have h_ite_v106 := (show if_3_eo__24eo_5fprog_5fconcat_5fcsplit s21 a0 v4 ⦃ r s' => s'.Inv ∧ s21.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_3_eo__24eo_5fprog_5fconcat_5fcsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s21
            rcases Store.boolean_value_term h_a0 with ⟨hx_100, hbv_100⟩ | ⟨hx_100, hbv_100⟩ | ⟨hx_100, hbv_100⟩
            · ite_branch hbv_100
              step as ⟨e_v100, he_v100⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v100 (by rw [he_v100]; exact empty_args) hinv21 h64 as ⟨v100, s22, hinv22, h_v100⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 dropping he_v100 e_v100
              step as ⟨e_v101, he_v101⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v101 (by rw [he_v101]; exact empty_args) hinv22 h64 as ⟨v101, s23, hinv23, h_v101⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 h_v100 dropping he_v101 e_v101
              step as ⟨e_v102, he_v102⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s23 e_v102 (by rw [he_v102]; rfl) h_v101 h_v4 hinv23 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v102, s24, hinv24, h_v102⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 h_v100 dropping h_v101 he_v102 e_v102 v101
              step as ⟨e_v103, he_v103⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s24 e_v103 (by rw [he_v103]; rfl) h_v100 h_v102 hinv24 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v103, s25, hinv25, h_v103⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 dropping h_v100 h_v102 he_v103 e_v103 v100 v102
              ite_done hinv25 hG with (eo_ite_true_rep _ hx_100 h_v103)
            · ite_branch hbv_100
              step as ⟨e_v104, he_v104⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v104 (by rw [he_v104]; exact empty_args) hinv21 h64 as ⟨v104, s22, hinv22, h_v104⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 dropping he_v104 e_v104
              step as ⟨e_v105, he_v105⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s22 e_v105 (by rw [he_v105]; rfl) h_v104 h_v4 hinv22 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v105, s23, hinv23, h_v105⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 dropping h_v104 he_v105 e_v105 v104
              ite_done hinv23 hG with (eo_ite_false_rep _ hx_100 h_v105)
            · ite_branch hbv_100
              ite_stuck hinv21 hG with hx_100)
          store_step with h_ite_v106 as ⟨v106, s22, hinv22, h_v106⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 dropping h_ite_v106
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s22 0#u32 (0) (by scalar_tac) hinv22 h64 as ⟨v107, s23, hinv23, h_v107⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 h_v99 h_v106 dropping
          step as ⟨e_v108, he_v108⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s23 e_v108 (by rw [he_v108]; rfl) h_v99 h_v106 h_v107 hinv23 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v108, s24, hinv24, h_v108⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v98 dropping h_v106 h_v107 h_v99 he_v108 e_v108 v106 v107 v99
          store_step with Store.apply_mk_rep s24 v98 v108 _ _ hinv24 h64 h_v98 h_v108 as ⟨v109, s25, hinv25, h_v109⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 dropping h_v108 h_v98 hinv24 s24 v108 v98
          step as ⟨e_v110, he_v110⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s25 e_v110 (by rw [he_v110]; exact empty_args) hinv25 h64 as ⟨v110, s26, hinv26, h_v110⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 dropping he_v110 hinv25 e_v110 s25
          step as ⟨e_v111, he_v111⟩
          store_step with CtorSpec.eo__40purify.construct s26 e_v111 (by rw [he_v111]; exact empty_args) hinv26 h64 as ⟨v111, s27, hinv27, h_v111⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 dropping he_v111 hinv26 e_v111 s26
          step as ⟨e_v112, he_v112⟩
          store_step with CtorSpec.eo_str_2esubstr.construct s27 e_v112 (by rw [he_v112]; exact empty_args) hinv27 h64 as ⟨v112, s28, hinv28, h_v112⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 h_v111 dropping he_v112 hinv27 e_v112 s27
          store_step with Store.apply_rep s28 v112 v24 _ _ hinv28 h64 h_v112 h_v24 (by ns_tac) (by ns_tac) as ⟨v113, s29, hinv29, h_v113⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 h_v111 dropping h_v112 hinv28 s28 v112
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v114, s30, hinv30, h_v114⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 h_v111 h_v113 dropping hinv29 s29
          store_step with Store.apply_rep s30 v113 v114 _ _ hinv30 h64 h_v113 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s31, hinv31, h_v115⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 h_v111 dropping h_v113 h_v114 hinv30 s30 v113 v114
          step as ⟨e_v116, he_v116⟩
          store_step with CtorSpec.eo__2d.construct s31 e_v116 (by rw [he_v116]; exact empty_args) hinv31 h64 as ⟨v116, s32, hinv32, h_v116⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 h_v111 h_v115 dropping he_v116 hinv31 e_v116 s31
          step as ⟨e_v117, he_v117⟩
          store_step with CtorSpec.eo_str_2elen.construct s32 e_v117 (by rw [he_v117]; exact empty_args) hinv32 h64 as ⟨v117, s33, hinv33, h_v117⟩ growing hG carrying h_a0 h_v4 h_v24 h_v52 h_v109 h_v110 h_v111 h_v115 h_v116 dropping he_v117 hinv32 e_v117 s32
          store_step with Store.apply_rep s33 v117 v24 _ _ hinv33 h64 h_v117 h_v24 (by ns_tac) (by ns_tac) as ⟨v118, s34, hinv34, h_v118⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v110 h_v111 h_v115 h_v116 dropping h_v117 h_v24 hinv33 s33 v117 v24
          store_step with Store.apply_rep s34 v116 v118 _ _ hinv34 h64 h_v116 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s35, hinv35, h_v119⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v110 h_v111 h_v115 dropping h_v116 h_v118 hinv34 s34 v116 v118
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s35 1#u32 (1) (by scalar_tac) hinv35 h64 as ⟨v120, s36, hinv36, h_v120⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v110 h_v111 h_v115 h_v119 dropping hinv35 s35
          store_step with Store.apply_rep s36 v119 v120 _ _ hinv36 h64 h_v119 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s37, hinv37, h_v121⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v110 h_v111 h_v115 dropping h_v119 h_v120 hinv36 s36 v119 v120
          store_step with Store.apply_rep s37 v115 v121 _ _ hinv37 h64 h_v115 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s38, hinv38, h_v122⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v110 h_v111 dropping h_v115 h_v121 hinv37 s37 v115 v121
          store_step with Store.apply_rep s38 v111 v122 _ _ hinv38 h64 h_v111 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s39, hinv39, h_v123⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v110 dropping h_v111 h_v122 hinv38 s38 v111 v122
          store_step with Store.apply_rep s39 v110 v123 _ _ hinv39 h64 h_v110 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s40, hinv40, h_v124⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 dropping h_v110 h_v123 hinv39 s39 v110 v123
          step as ⟨e_v125, he_v125⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v125 (by rw [he_v125]; exact empty_args) hinv40 h64 as ⟨v125, s41, hinv41, h_v125⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v124 dropping he_v125 hinv40 e_v125 s40
          step as ⟨e_v126, he_v126⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v126 (by rw [he_v126]; exact empty_args) hinv41 h64 as ⟨v126, s42, hinv42, h_v126⟩ growing hG carrying h_a0 h_v4 h_v52 h_v109 h_v124 h_v125 dropping he_v126 hinv41 e_v126 s41
          have h_ite_v133 := (show if_4_eo__24eo_5fprog_5fconcat_5fcsplit s42 a0 v4 ⦃ r s' => s'.Inv ∧ s42.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_4_eo__24eo_5fprog_5fconcat_5fcsplit
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s42
            rcases Store.boolean_value_term h_a0 with ⟨hx_127, hbv_127⟩ | ⟨hx_127, hbv_127⟩ | ⟨hx_127, hbv_127⟩
            · ite_branch hbv_127
              step as ⟨e_v127, he_v127⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v127 (by rw [he_v127]; exact empty_args) hinv42 h64 as ⟨v127, s43, hinv43, h_v127⟩ growing hG carrying h_v4 h_v52 h_v109 h_v124 h_v125 h_v126 dropping h_a0 he_v127 e_v127
              step as ⟨e_v128, he_v128⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v128 (by rw [he_v128]; exact empty_args) hinv43 h64 as ⟨v128, s44, hinv44, h_v128⟩ growing hG carrying h_v4 h_v52 h_v109 h_v124 h_v125 h_v126 h_v127 dropping he_v128 e_v128
              step as ⟨e_v129, he_v129⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s44 e_v129 (by rw [he_v129]; rfl) h_v128 h_v4 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v129, s45, hinv45, h_v129⟩ growing hG carrying h_v4 h_v52 h_v109 h_v124 h_v125 h_v126 h_v127 dropping h_v128 he_v129 e_v129 v128
              step as ⟨e_v130, he_v130⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s45 e_v130 (by rw [he_v130]; rfl) h_v127 h_v129 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v130, s46, hinv46, h_v130⟩ growing hG carrying h_v4 h_v52 h_v109 h_v124 h_v125 h_v126 dropping h_v127 h_v129 he_v130 e_v130 v127 v129
              ite_done hinv46 hG with (eo_ite_true_rep _ hx_127 h_v130)
            · ite_branch hbv_127
              step as ⟨e_v131, he_v131⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v131 (by rw [he_v131]; exact empty_args) hinv42 h64 as ⟨v131, s43, hinv43, h_v131⟩ growing hG carrying h_v4 h_v52 h_v109 h_v124 h_v125 h_v126 dropping h_a0 he_v131 e_v131
              step as ⟨e_v132, he_v132⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s43 e_v132 (by rw [he_v132]; rfl) h_v131 h_v4 hinv43 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v132, s44, hinv44, h_v132⟩ growing hG carrying h_v52 h_v109 h_v124 h_v125 h_v126 dropping h_v131 h_v4 he_v132 e_v132 v131 v4
              ite_done hinv44 hG with (eo_ite_false_rep _ hx_127 h_v132)
            · ite_branch hbv_127
              ite_stuck hinv42 hG with hx_127)
          store_step with h_ite_v133 as ⟨v133, s43, hinv43, h_v133⟩ growing hG carrying h_v52 h_v109 h_v124 h_v125 h_v126 dropping h_a0 h_ite_v133 h_v4 hinv42 s42 v4
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s43 0#u32 (0) (by scalar_tac) hinv43 h64 as ⟨v134, s44, hinv44, h_v134⟩ growing hG carrying h_v52 h_v109 h_v124 h_v125 h_v126 h_v133 dropping hinv43 s43
          step as ⟨e_v135, he_v135⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s44 e_v135 (by rw [he_v135]; rfl) h_v126 h_v133 h_v134 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v135, s45, hinv45, h_v135⟩ growing hG carrying h_v52 h_v109 h_v124 h_v125 dropping h_v126 h_v133 h_v134 he_v135 hinv44 e_v135 s44 v126 v133 v134
          store_step with ih.eo__24eo_5ftypeof s45 v135 _ hinv45 h64 (hG.rem hrem) h_v135 as ⟨v136, s46, hinv46, h_v136⟩ growing hG carrying h_v52 h_v109 h_v124 h_v125 dropping h_v135 hinv45 s45 v135
          store_step with ih.eo__24eo_5fnil s46 v125 v136 _ _ hinv46 h64 (hG.rem hrem) h_v125 h_v136 as ⟨v137, s47, hinv47, h_v137⟩ growing hG carrying h_v52 h_v109 h_v124 dropping h_v125 h_v136 hinv46 s46 v125 v136
          store_step with Store.apply_mk_rep s47 v124 v137 _ _ hinv47 h64 h_v124 h_v137 as ⟨v138, s48, hinv48, h_v138⟩ growing hG carrying h_v52 h_v109 dropping h_v124 h_v137 hinv47 s47 v124 v137
          store_step with Store.apply_mk_rep s48 v109 v138 _ _ hinv48 h64 h_v109 h_v138 as ⟨v139, s49, hinv49, h_v139⟩ growing hG carrying h_v52 dropping h_v109 h_v138 hinv48 s48 v109 v138
          ite_done hinv49 hG with (eo_ite_false_rep _ hx_53 h_v139)
        · ite_branch hbv_53
          ite_stuck hinv19 hG with hx_53)
      store_step with h_ite_v140 as ⟨v140, s20, hinv20, h_v140⟩ growing hG carrying h_v52 dropping h_ite_v140 h_v24 h_v4 hinv19 s19 v24 v4
      store_step with Store.apply_mk_rep s20 v52 v140 _ _ hinv20 h64 h_v52 h_v140 as ⟨v141, s21, hinv21, h_v141⟩ growing hG carrying dropping h_v140 h_v52 hinv20 s20 v140 v52
      req_done hinv21 hG with h_v141 using hq_v49)
    store_step with h_req_v142 as ⟨v142, s22, hinv22, h_v142⟩ growing hG carrying dropping h_req_v142 h_v24 h_v4 h_v49 h_v50 hinv17 s17 v24 v4 v49 v50
    req_done hinv22 hG with h_v142 using hq_v36)
  store_step with h_req_v143 as ⟨v143, s23, hinv23, h_v143⟩ growing hG carrying dropping h_req_v143 h_v24 h_v36 h_v4 hinv9 s9 v24 v36 v4
  case_done hinv23 hG with h_v143 in EoCases.__eo_prog_concat_csplit.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v12 hn_v13 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24

/-- logos's `__eo_prog_concat_csplit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5fcsplit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_concat_csplit x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_csplit.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_csplit
  unfold EoCases.__eo_prog_concat_csplit.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fconcat_5fcsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fconcat_5fcsplit s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_csplit x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5fcsplit.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fconcat_5fcsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5fcsplit_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_csplit.case_0

theorem eo__24eo_5fprog_5fconcat_5fcsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5fcsplit.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fconcat_5fcsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5fcsplit s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_concat_csplit x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5fcsplit_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

set_option maxHeartbeats 2340000 in
theorem case_0_eo__24eo_5fprog_5fconcat_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_eq.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_eq.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5feq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_eq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_eq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_eq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_eq.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v6 h_v8 he_v9 hinv1 e_v9 s1 v6 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 dropping he_v10 hinv2 e_v10 s2
  have h_ite_v45 := (show if_4_eo__24eo_5fprog_5fconcat_5feq s3 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_4_eo__24eo_5fprog_5fconcat_5feq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_a0 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      step as ⟨e_v11, he_v11⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping he_v11 e_v11
      have h_ite_v18 := (show if_0_eo__24eo_5fprog_5fconcat_5feq s4 a0 v7 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_a0 with ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩ | ⟨hx_12, hbv_12⟩
        · ite_branch hbv_12
          step as ⟨e_v12, he_v12⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v12 (by rw [he_v12]; exact empty_args) hinv4 h64 as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping he_v12 e_v12
          step as ⟨e_v13, he_v13⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v12 dropping he_v13 e_v13
          step as ⟨e_v14, he_v14⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v14 (by rw [he_v14]; rfl) h_v13 h_v7 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v12 dropping h_v13 he_v14 e_v14 v13
          step as ⟨e_v15, he_v15⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s7 e_v15 (by rw [he_v15]; rfl) h_v12 h_v14 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v12 h_v14 he_v15 e_v15 v12 v14
          ite_done hinv8 hG with (eo_ite_true_rep _ hx_12 h_v15)
        · ite_branch hbv_12
          step as ⟨e_v16, he_v16⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping he_v16 e_v16
          step as ⟨e_v17, he_v17⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s5 e_v17 (by rw [he_v17]; rfl) h_v16 h_v7 hinv5 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v16 he_v17 e_v17 v16
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_12 h_v17)
        · ite_branch hbv_12
          ite_stuck hinv4 hG with hx_12)
      store_step with h_ite_v18 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_ite_v18
      have h_ite_v25 := (show if_1_eo__24eo_5fprog_5fconcat_5feq s5 a0 v4 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_1_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s5
        rcases Store.boolean_value_term h_a0 with ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩ | ⟨hx_19, hbv_19⟩
        · ite_branch hbv_19
          step as ⟨e_v19, he_v19⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping he_v19 e_v19
          step as ⟨e_v20, he_v20⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 h_v19 dropping he_v20 e_v20
          step as ⟨e_v21, he_v21⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v21 (by rw [he_v21]; rfl) h_v20 h_v4 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 h_v19 dropping h_v20 he_v21 e_v21 v20
          step as ⟨e_v22, he_v22⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s8 e_v22 (by rw [he_v22]; rfl) h_v19 h_v21 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping h_v19 h_v21 he_v22 e_v22 v19 v21
          ite_done hinv9 hG with (eo_ite_true_rep _ hx_19 h_v22)
        · ite_branch hbv_19
          step as ⟨e_v23, he_v23⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v23 (by rw [he_v23]; exact empty_args) hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping he_v23 e_v23
          step as ⟨e_v24, he_v24⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v24 (by rw [he_v24]; rfl) h_v23 h_v4 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping h_v23 he_v24 e_v24 v23
          ite_done hinv7 hG with (eo_ite_false_rep _ hx_19 h_v24)
        · ite_branch hbv_19
          ite_stuck hinv5 hG with hx_19)
      store_step with h_ite_v25 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 h_v18 dropping h_ite_v25
      store_step with ih.eo__24str_5fstrip_5fprefix s6 v18 v25 _ _ hinv6 h64 (hG.rem hrem) h_v18 h_v25 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v18 h_v25 v18 v25
      store_step with ih.eo__24pair_5ffirst s7 v26 _ hinv7 h64 (hG.rem hrem) h_v26 as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v11 dropping h_v26 v26
      step as ⟨e_v28, he_v28⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s8 e_v28 (by rw [he_v28]; rfl) h_v11 h_v27 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v11 h_v27 he_v28 e_v28 v11 v27
      ite_done hinv9 hG with (eo_ite_true_rep _ hx_11 h_v28)
    · ite_branch hbv_11
      have h_ite_v35 := (show if_2_eo__24eo_5fprog_5fconcat_5feq s3 a0 v7 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s3
        rcases Store.boolean_value_term h_a0 with ⟨hx_29, hbv_29⟩ | ⟨hx_29, hbv_29⟩ | ⟨hx_29, hbv_29⟩
        · ite_branch hbv_29
          step as ⟨e_v29, he_v29⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v29 (by rw [he_v29]; exact empty_args) hinv3 h64 as ⟨v29, s4, hinv4, h_v29⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping he_v29 e_v29
          step as ⟨e_v30, he_v30⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v30 (by rw [he_v30]; exact empty_args) hinv4 h64 as ⟨v30, s5, hinv5, h_v30⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v29 dropping he_v30 e_v30
          step as ⟨e_v31, he_v31⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s5 e_v31 (by rw [he_v31]; rfl) h_v30 h_v7 hinv5 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v31, s6, hinv6, h_v31⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v29 dropping h_v30 he_v31 e_v31 v30
          step as ⟨e_v32, he_v32⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s6 e_v32 (by rw [he_v32]; rfl) h_v29 h_v31 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v29 h_v31 he_v32 e_v32 v29 v31
          ite_done hinv7 hG with (eo_ite_true_rep _ hx_29 h_v32)
        · ite_branch hbv_29
          step as ⟨e_v33, he_v33⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s3 e_v33 (by rw [he_v33]; exact empty_args) hinv3 h64 as ⟨v33, s4, hinv4, h_v33⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping he_v33 e_v33
          step as ⟨e_v34, he_v34⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s4 e_v34 (by rw [he_v34]; rfl) h_v33 h_v7 hinv4 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v34, s5, hinv5, h_v34⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v33 he_v34 e_v34 v33
          ite_done hinv5 hG with (eo_ite_false_rep _ hx_29 h_v34)
        · ite_branch hbv_29
          ite_stuck hinv3 hG with hx_29)
      store_step with h_ite_v35 as ⟨v35, s4, hinv4, h_v35⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_ite_v35
      have h_ite_v42 := (show if_3_eo__24eo_5fprog_5fconcat_5feq s4 a0 v4 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_3_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s4
        rcases Store.boolean_value_term h_a0 with ⟨hx_36, hbv_36⟩ | ⟨hx_36, hbv_36⟩ | ⟨hx_36, hbv_36⟩
        · ite_branch hbv_36
          step as ⟨e_v36, he_v36⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v36 (by rw [he_v36]; exact empty_args) hinv4 h64 as ⟨v36, s5, hinv5, h_v36⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping he_v36 e_v36
          step as ⟨e_v37, he_v37⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v37 (by rw [he_v37]; exact empty_args) hinv5 h64 as ⟨v37, s6, hinv6, h_v37⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 h_v36 dropping he_v37 e_v37
          step as ⟨e_v38, he_v38⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v38 (by rw [he_v38]; rfl) h_v37 h_v4 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v38, s7, hinv7, h_v38⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 h_v36 dropping h_v37 he_v38 e_v38 v37
          step as ⟨e_v39, he_v39⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s7 e_v39 (by rw [he_v39]; rfl) h_v36 h_v38 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v39, s8, hinv8, h_v39⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping h_v36 h_v38 he_v39 e_v39 v36 v38
          ite_done hinv8 hG with (eo_ite_true_rep _ hx_36 h_v39)
        · ite_branch hbv_36
          step as ⟨e_v40, he_v40⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v40 (by rw [he_v40]; exact empty_args) hinv4 h64 as ⟨v40, s5, hinv5, h_v40⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping he_v40 e_v40
          step as ⟨e_v41, he_v41⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s5 e_v41 (by rw [he_v41]; rfl) h_v40 h_v4 hinv5 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v41, s6, hinv6, h_v41⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping h_v40 he_v41 e_v41 v40
          ite_done hinv6 hG with (eo_ite_false_rep _ hx_36 h_v41)
        · ite_branch hbv_36
          ite_stuck hinv4 hG with hx_36)
      store_step with h_ite_v42 as ⟨v42, s5, hinv5, h_v42⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 h_v35 dropping h_ite_v42
      store_step with ih.eo__24str_5fstrip_5fprefix s5 v35 v42 _ _ hinv5 h64 (hG.rem hrem) h_v35 h_v42 as ⟨v43, s6, hinv6, h_v43⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v35 h_v42 v35 v42
      store_step with ih.eo__24pair_5ffirst s6 v43 _ hinv6 h64 (hG.rem hrem) h_v43 as ⟨v44, s7, hinv7, h_v44⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_v43 v43
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_11 h_v44)
    · ite_branch hbv_11
      ite_stuck hinv3 hG with hx_11)
  store_step with h_ite_v45 as ⟨v45, s4, hinv4, h_v45⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 h_v10 dropping h_ite_v45 hinv3 s3
  step as ⟨e_v46, he_v46⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s4 e_v46 (by rw [he_v46]; rfl) h_v10 h_v45 hinv4 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v46, s5, hinv5, h_v46⟩ growing hG carrying h_a0 h_v4 h_v7 h_v9 dropping h_v10 h_v45 he_v46 hinv4 e_v46 s4 v10 v45
  store_step with Store.apply_mk_rep s5 v9 v46 _ _ hinv5 h64 h_v9 h_v46 as ⟨v47, s6, hinv6, h_v47⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v46 h_v9 hinv5 s5 v46 v9
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v48 (by rw [he_v48]; exact empty_args) hinv6 h64 as ⟨v48, s7, hinv7, h_v48⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 dropping he_v48 hinv6 e_v48 s6
  have h_ite_v83 := (show if_9_eo__24eo_5fprog_5fconcat_5feq s7 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_9_eo__24eo_5fprog_5fconcat_5feq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    rcases Store.boolean_value_term h_a0 with ⟨hx_49, hbv_49⟩ | ⟨hx_49, hbv_49⟩ | ⟨hx_49, hbv_49⟩
    · ite_branch hbv_49
      step as ⟨e_v49, he_v49⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v49 (by rw [he_v49]; exact empty_args) hinv7 h64 as ⟨v49, s8, hinv8, h_v49⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping he_v49 e_v49
      have h_ite_v56 := (show if_5_eo__24eo_5fprog_5fconcat_5feq s8 a0 v7 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_5_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_term h_a0 with ⟨hx_50, hbv_50⟩ | ⟨hx_50, hbv_50⟩ | ⟨hx_50, hbv_50⟩
        · ite_branch hbv_50
          step as ⟨e_v50, he_v50⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v50 (by rw [he_v50]; exact empty_args) hinv8 h64 as ⟨v50, s9, hinv9, h_v50⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping he_v50 e_v50
          step as ⟨e_v51, he_v51⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v50 dropping he_v51 e_v51
          step as ⟨e_v52, he_v52⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v52 (by rw [he_v52]; rfl) h_v51 h_v7 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v52, s11, hinv11, h_v52⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v50 dropping h_v51 he_v52 e_v52 v51
          step as ⟨e_v53, he_v53⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s11 e_v53 (by rw [he_v53]; rfl) h_v50 h_v52 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v53, s12, hinv12, h_v53⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v50 h_v52 he_v53 e_v53 v50 v52
          ite_done hinv12 hG with (eo_ite_true_rep _ hx_50 h_v53)
        · ite_branch hbv_50
          step as ⟨e_v54, he_v54⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v54 (by rw [he_v54]; exact empty_args) hinv8 h64 as ⟨v54, s9, hinv9, h_v54⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping he_v54 e_v54
          step as ⟨e_v55, he_v55⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s9 e_v55 (by rw [he_v55]; rfl) h_v54 h_v7 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v55, s10, hinv10, h_v55⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v54 he_v55 e_v55 v54
          ite_done hinv10 hG with (eo_ite_false_rep _ hx_50 h_v55)
        · ite_branch hbv_50
          ite_stuck hinv8 hG with hx_50)
      store_step with h_ite_v56 as ⟨v56, s9, hinv9, h_v56⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_ite_v56
      have h_ite_v63 := (show if_6_eo__24eo_5fprog_5fconcat_5feq s9 a0 v4 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_6_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s9
        rcases Store.boolean_value_term h_a0 with ⟨hx_57, hbv_57⟩ | ⟨hx_57, hbv_57⟩ | ⟨hx_57, hbv_57⟩
        · ite_branch hbv_57
          step as ⟨e_v57, he_v57⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v57 (by rw [he_v57]; exact empty_args) hinv9 h64 as ⟨v57, s10, hinv10, h_v57⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping he_v57 e_v57
          step as ⟨e_v58, he_v58⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 h_v57 dropping he_v58 e_v58
          step as ⟨e_v59, he_v59⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v59 (by rw [he_v59]; rfl) h_v58 h_v4 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v59, s12, hinv12, h_v59⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 h_v57 dropping h_v58 he_v59 e_v59 v58
          step as ⟨e_v60, he_v60⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v60 (by rw [he_v60]; rfl) h_v57 h_v59 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v60, s13, hinv13, h_v60⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping h_v57 h_v59 he_v60 e_v60 v57 v59
          ite_done hinv13 hG with (eo_ite_true_rep _ hx_57 h_v60)
        · ite_branch hbv_57
          step as ⟨e_v61, he_v61⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v61 (by rw [he_v61]; exact empty_args) hinv9 h64 as ⟨v61, s10, hinv10, h_v61⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping he_v61 e_v61
          step as ⟨e_v62, he_v62⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v62 (by rw [he_v62]; rfl) h_v61 h_v4 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v62, s11, hinv11, h_v62⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping h_v61 he_v62 e_v62 v61
          ite_done hinv11 hG with (eo_ite_false_rep _ hx_57 h_v62)
        · ite_branch hbv_57
          ite_stuck hinv9 hG with hx_57)
      store_step with h_ite_v63 as ⟨v63, s10, hinv10, h_v63⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 h_v56 dropping h_ite_v63
      store_step with ih.eo__24str_5fstrip_5fprefix s10 v56 v63 _ _ hinv10 h64 (hG.rem hrem) h_v56 h_v63 as ⟨v64, s11, hinv11, h_v64⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v56 h_v63 v56 v63
      store_step with ih.eo__24pair_5fsecond s11 v64 _ hinv11 h64 (hG.rem hrem) h_v64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v49 dropping h_v64 v64
      step as ⟨e_v66, he_v66⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v66 (by rw [he_v66]; rfl) h_v49 h_v65 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping h_v49 h_v65 he_v66 e_v66 v49 v65
      ite_done hinv13 hG with (eo_ite_true_rep _ hx_49 h_v66)
    · ite_branch hbv_49
      have h_ite_v73 := (show if_7_eo__24eo_5fprog_5fconcat_5feq s7 a0 v7 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_7_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s7
        rcases Store.boolean_value_term h_a0 with ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩
        · ite_branch hbv_67
          step as ⟨e_v67, he_v67⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v67 (by rw [he_v67]; exact empty_args) hinv7 h64 as ⟨v67, s8, hinv8, h_v67⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping he_v67 e_v67
          step as ⟨e_v68, he_v68⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v68 (by rw [he_v68]; exact empty_args) hinv8 h64 as ⟨v68, s9, hinv9, h_v68⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v67 dropping he_v68 e_v68
          step as ⟨e_v69, he_v69⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s9 e_v69 (by rw [he_v69]; rfl) h_v68 h_v7 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v69, s10, hinv10, h_v69⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 h_v67 dropping h_v68 he_v69 e_v69 v68
          step as ⟨e_v70, he_v70⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s10 e_v70 (by rw [he_v70]; rfl) h_v67 h_v69 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v70, s11, hinv11, h_v70⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping h_v67 h_v69 he_v70 e_v70 v67 v69
          ite_done hinv11 hG with (eo_ite_true_rep _ hx_67 h_v70)
        · ite_branch hbv_67
          step as ⟨e_v71, he_v71⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v71 (by rw [he_v71]; exact empty_args) hinv7 h64 as ⟨v71, s8, hinv8, h_v71⟩ growing hG carrying h_a0 h_v4 h_v7 h_v47 h_v48 dropping he_v71 e_v71
          step as ⟨e_v72, he_v72⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s8 e_v72 (by rw [he_v72]; rfl) h_v71 h_v7 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v72, s9, hinv9, h_v72⟩ growing hG carrying h_a0 h_v4 h_v47 h_v48 dropping h_v7 h_v71 he_v72 e_v72 v7 v71
          ite_done hinv9 hG with (eo_ite_false_rep _ hx_67 h_v72)
        · ite_branch hbv_67
          ite_stuck hinv7 hG with hx_67)
      store_step with h_ite_v73 as ⟨v73, s8, hinv8, h_v73⟩ growing hG carrying h_a0 h_v4 h_v47 h_v48 dropping h_ite_v73 h_v7 v7
      have h_ite_v80 := (show if_8_eo__24eo_5fprog_5fconcat_5feq s8 a0 v4 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_8_eo__24eo_5fprog_5fconcat_5feq
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s8
        rcases Store.boolean_value_term h_a0 with ⟨hx_74, hbv_74⟩ | ⟨hx_74, hbv_74⟩ | ⟨hx_74, hbv_74⟩
        · ite_branch hbv_74
          step as ⟨e_v74, he_v74⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v74 (by rw [he_v74]; exact empty_args) hinv8 h64 as ⟨v74, s9, hinv9, h_v74⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 dropping h_a0 he_v74 e_v74
          step as ⟨e_v75, he_v75⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v75 (by rw [he_v75]; exact empty_args) hinv9 h64 as ⟨v75, s10, hinv10, h_v75⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 h_v74 dropping he_v75 e_v75
          step as ⟨e_v76, he_v76⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v76 (by rw [he_v76]; rfl) h_v75 h_v4 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v76, s11, hinv11, h_v76⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 h_v74 dropping h_v75 he_v76 e_v76 v75
          step as ⟨e_v77, he_v77⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s11 e_v77 (by rw [he_v77]; rfl) h_v74 h_v76 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v77, s12, hinv12, h_v77⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 dropping h_v74 h_v76 he_v77 e_v77 v74 v76
          ite_done hinv12 hG with (eo_ite_true_rep _ hx_74 h_v77)
        · ite_branch hbv_74
          step as ⟨e_v78, he_v78⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v78 (by rw [he_v78]; exact empty_args) hinv8 h64 as ⟨v78, s9, hinv9, h_v78⟩ growing hG carrying h_v4 h_v47 h_v48 h_v73 dropping h_a0 he_v78 e_v78
          step as ⟨e_v79, he_v79⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s9 e_v79 (by rw [he_v79]; rfl) h_v78 h_v4 hinv9 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v79, s10, hinv10, h_v79⟩ growing hG carrying h_v47 h_v48 h_v73 dropping h_v4 h_v78 he_v79 e_v79 v4 v78
          ite_done hinv10 hG with (eo_ite_false_rep _ hx_74 h_v79)
        · ite_branch hbv_74
          ite_stuck hinv8 hG with hx_74)
      store_step with h_ite_v80 as ⟨v80, s9, hinv9, h_v80⟩ growing hG carrying h_v47 h_v48 h_v73 dropping h_a0 h_ite_v80 h_v4 v4
      store_step with ih.eo__24str_5fstrip_5fprefix s9 v73 v80 _ _ hinv9 h64 (hG.rem hrem) h_v73 h_v80 as ⟨v81, s10, hinv10, h_v81⟩ growing hG carrying h_v47 h_v48 dropping h_v73 h_v80 v73 v80
      store_step with ih.eo__24pair_5fsecond s10 v81 _ hinv10 h64 (hG.rem hrem) h_v81 as ⟨v82, s11, hinv11, h_v82⟩ growing hG carrying h_v47 h_v48 dropping h_v81 v81
      ite_done hinv11 hG with (eo_ite_false_rep _ hx_49 h_v82)
    · ite_branch hbv_49
      ite_stuck hinv7 hG with hx_49)
  store_step with h_ite_v83 as ⟨v83, s8, hinv8, h_v83⟩ growing hG carrying h_v47 h_v48 dropping h_ite_v83 h_v4 h_v7 hinv7 s7 v4 v7
  step as ⟨e_v84, he_v84⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s8 e_v84 (by rw [he_v84]; rfl) h_v48 h_v83 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v84, s9, hinv9, h_v84⟩ growing hG carrying h_v47 dropping h_v48 h_v83 he_v84 hinv8 e_v84 s8 v48 v83
  store_step with Store.apply_mk_rep s9 v47 v84 _ _ hinv9 h64 h_v47 h_v84 as ⟨v85, s10, hinv10, h_v85⟩ growing hG carrying dropping h_v47 h_v84 hinv9 s9 v47 v84
  case_done hinv10 hG with h_v85 in EoCases.__eo_prog_concat_eq.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_concat_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5feq.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_concat_eq x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_eq.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_eq
  unfold EoCases.__eo_prog_concat_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fconcat_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fconcat_5feq s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_eq x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5feq.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fconcat_5feq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5feq_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_eq.case_0

theorem eo__24eo_5fprog_5fconcat_5feq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5feq.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fconcat_5feq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5feq s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_concat_eq x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5feq_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

set_option maxHeartbeats 7470000 in
theorem case_0_eo__24eo_5fprog_5fconcat_5flprop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fconcat_5flprop s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_concat_lprop.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_concat_lprop.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fconcat_5flprop
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_concat_lprop.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a2 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v10, x_v10, h_v10⟩ else hinv1 hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_unapply h_v10 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_concat_lprop.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v17 (by rw [he_v17]; exact empty_args) hinv1 h64 as ⟨v17, s2, hinv2, h_v17⟩ growing hG carrying h_a0 h_v4 h_v7 h_v13 h_v15 h_v16 dropping h_a2 h_v10 h_v12 h_v6 h_v8 he_v17 hinv1 e_v17 s1 v10 v12 v6 v8
  pat_same v15 v17 with h_v15 h_v17 using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_concat_lprop.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_v4 h_v7 h_v13 h_v19 h_v20 dropping h_v15 h_v16 h_v17 he_v21 hinv2 e_v21 s2 v15 v16 v17
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_lprop.case_0
  pat_unapply h_v13 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_concat_lprop.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v23 h_v24 dropping h_v13 h_v19 h_v21 he_v25 hinv3 e_v25 s3 v13 v19 v21
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_concat_lprop.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 dropping h_v23 h_v25 he_v26 hinv4 e_v26 s4 v23 v25
  have h_ite_v33 := (show if_0_eo__24eo_5fprog_5fconcat_5flprop s5 a0 v7 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fprog_5fconcat_5flprop
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    rcases Store.boolean_value_term h_a0 with ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩
    · ite_branch hbv_27
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping he_v27 e_v27
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 h_v27 dropping he_v28 e_v28
      step as ⟨e_v29, he_v29⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s7 e_v29 (by rw [he_v29]; rfl) h_v28 h_v7 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 h_v27 dropping h_v28 he_v29 e_v29 v28
      step as ⟨e_v30, he_v30⟩
      store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s8 e_v30 (by rw [he_v30]; rfl) h_v27 h_v29 hinv8 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping h_v27 h_v29 he_v30 e_v30 v27 v29
      ite_done hinv9 hG with (eo_ite_true_rep _ hx_27 h_v30)
    · ite_branch hbv_27
      step as ⟨e_v31, he_v31⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v31 (by rw [he_v31]; exact empty_args) hinv5 h64 as ⟨v31, s6, hinv6, h_v31⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping he_v31 e_v31
      step as ⟨e_v32, he_v32⟩
      store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s6 e_v32 (by rw [he_v32]; rfl) h_v31 h_v7 hinv6 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v32, s7, hinv7, h_v32⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping h_v31 he_v32 e_v32 v31
      ite_done hinv7 hG with (eo_ite_false_rep _ hx_27 h_v32)
    · ite_branch hbv_27
      ite_stuck hinv5 hG with hx_27)
  store_step with h_ite_v33 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 dropping h_ite_v33 hinv5 s5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 h_v26 h_v33 dropping hinv6 s6
  step as ⟨e_v35, he_v35⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s7 e_v35 (by rw [he_v35]; rfl) h_v26 h_v33 h_v34 hinv7 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_v4 h_v7 h_v20 h_v24 dropping h_v26 h_v33 h_v34 he_v35 hinv7 e_v35 s7 v26 v33 v34
  have h_req_v270 := (show requires_29_eo__24eo_5fprog_5fconcat_5flprop s8 v35 v20 a0 v4 v24 v7 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_29_eo__24eo_5fprog_5fconcat_5flprop
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v35 v20 with h_v35 h_v20 using hinv8 hG
    req_stuck h_v35 as hq_v35 using hinv8 hG
    step as ⟨e_v36, he_v36⟩
    store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v36 (by rw [he_v36]; exact empty_args) hinv8 h64 as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 dropping h_v20 h_v35 he_v36 hinv8 e_v36 s8 v20 v35
    have h_ite_v43 := (show if_1_eo__24eo_5fprog_5fconcat_5flprop s9 a0 v4 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_1_eo__24eo_5fprog_5fconcat_5flprop
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s9
      rcases Store.boolean_value_term h_a0 with ⟨hx_37, hbv_37⟩ | ⟨hx_37, hbv_37⟩ | ⟨hx_37, hbv_37⟩
      · ite_branch hbv_37
        step as ⟨e_v37, he_v37⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 dropping he_v37 e_v37
        step as ⟨e_v38, he_v38⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v38 (by rw [he_v38]; exact empty_args) hinv10 h64 as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 h_v37 dropping he_v38 e_v38
        step as ⟨e_v39, he_v39⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v39 (by rw [he_v39]; rfl) h_v38 h_v4 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 h_v37 dropping h_v38 he_v39 e_v39 v38
        step as ⟨e_v40, he_v40⟩
        store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v40 (by rw [he_v40]; rfl) h_v37 h_v39 hinv12 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 dropping h_v37 h_v39 he_v40 e_v40 v37 v39
        ite_done hinv13 hG with (eo_ite_true_rep _ hx_37 h_v40)
      · ite_branch hbv_37
        step as ⟨e_v41, he_v41⟩
        store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v41 (by rw [he_v41]; exact empty_args) hinv9 h64 as ⟨v41, s10, hinv10, h_v41⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 dropping he_v41 e_v41
        step as ⟨e_v42, he_v42⟩
        store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s10 e_v42 (by rw [he_v42]; rfl) h_v41 h_v4 hinv10 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v42, s11, hinv11, h_v42⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 dropping h_v41 he_v42 e_v42 v41
        ite_done hinv11 hG with (eo_ite_false_rep _ hx_37 h_v42)
      · ite_branch hbv_37
        ite_stuck hinv9 hG with hx_37)
    store_step with h_ite_v43 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 dropping h_ite_v43 hinv9 s9
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 h_v36 h_v43 dropping hinv10 s10
    step as ⟨e_v45, he_v45⟩
    store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s11 e_v45 (by rw [he_v45]; rfl) h_v36 h_v43 h_v44 hinv11 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_v4 h_v7 h_v24 dropping h_v36 h_v43 h_v44 he_v45 hinv11 e_v45 s11 v36 v43 v44
    have h_req_v269 := (show requires_28_eo__24eo_5fprog_5fconcat_5flprop s12 v45 v24 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s12.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_28_eo__24eo_5fprog_5fconcat_5flprop
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s12
      req_same v45 v24 with h_v45 h_v24 using hinv12 hG
      req_stuck h_v45 as hq_v45 using hinv12 hG
      step as ⟨e_v46, he_v46⟩
      store_step with CtorSpec.eo_and.construct s12 e_v46 (by rw [he_v46]; exact empty_args) hinv12 h64 as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v24 h_v45 he_v46 hinv12 e_v46 s12 v24 v45
      step as ⟨e_v47, he_v47⟩
      store_step with CtorSpec.eo__3d.construct s13 e_v47 (by rw [he_v47]; exact empty_args) hinv13 h64 as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 dropping he_v47 hinv13 e_v47 s13
      step as ⟨e_v48, he_v48⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v48 (by rw [he_v48]; exact empty_args) hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 dropping he_v48 hinv14 e_v48 s14
      have h_ite_v55 := (show if_2_eo__24eo_5fprog_5fconcat_5flprop s15 a0 v7 ⦃ r s' => s'.Inv ∧ s15.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_2_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s15
        rcases Store.boolean_value_term h_a0 with ⟨hx_49, hbv_49⟩ | ⟨hx_49, hbv_49⟩ | ⟨hx_49, hbv_49⟩
        · ite_branch hbv_49
          step as ⟨e_v49, he_v49⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s15 e_v49 (by rw [he_v49]; exact empty_args) hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 dropping he_v49 e_v49
          step as ⟨e_v50, he_v50⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v50 (by rw [he_v50]; exact empty_args) hinv16 h64 as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 h_v49 dropping he_v50 e_v50
          step as ⟨e_v51, he_v51⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s17 e_v51 (by rw [he_v51]; rfl) h_v50 h_v7 hinv17 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 h_v49 dropping h_v50 he_v51 e_v51 v50
          step as ⟨e_v52, he_v52⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s18 e_v52 (by rw [he_v52]; rfl) h_v49 h_v51 hinv18 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 dropping h_v49 h_v51 he_v52 e_v52 v49 v51
          ite_done hinv19 hG with (eo_ite_true_rep _ hx_49 h_v52)
        · ite_branch hbv_49
          step as ⟨e_v53, he_v53⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s15 e_v53 (by rw [he_v53]; exact empty_args) hinv15 h64 as ⟨v53, s16, hinv16, h_v53⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 dropping he_v53 e_v53
          step as ⟨e_v54, he_v54⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s16 e_v54 (by rw [he_v54]; rfl) h_v53 h_v7 hinv16 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v54, s17, hinv17, h_v54⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 dropping h_v53 he_v54 e_v54 v53
          ite_done hinv17 hG with (eo_ite_false_rep _ hx_49 h_v54)
        · ite_branch hbv_49
          ite_stuck hinv15 hG with hx_49)
      store_step with h_ite_v55 as ⟨v55, s16, hinv16, h_v55⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 dropping h_ite_v55 hinv15 s15
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v56, s17, hinv17, h_v56⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 h_v48 h_v55 dropping hinv16 s16
      step as ⟨e_v57, he_v57⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s17 e_v57 (by rw [he_v57]; rfl) h_v48 h_v55 h_v56 hinv17 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v57, s18, hinv18, h_v57⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v47 dropping h_v48 h_v55 h_v56 he_v57 hinv17 e_v57 s17 v48 v55 v56
      store_step with Store.apply_mk_rep s18 v47 v57 _ _ hinv18 h64 h_v47 h_v57 as ⟨v58, s19, hinv19, h_v58⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 dropping h_v47 h_v57 hinv18 s18 v47 v57
      have h_ite_v176 := (show if_16_eo__24eo_5fprog_5fconcat_5flprop s19 a0 a0 v7 v4 ⦃ r s' => s'.Inv ∧ s19.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_16_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s19
        rcases Store.boolean_value_term h_a0 with ⟨hx_59, hbv_59⟩ | ⟨hx_59, hbv_59⟩ | ⟨hx_59, hbv_59⟩
        · ite_branch hbv_59
          step as ⟨e_v59, he_v59⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v59 (by rw [he_v59]; exact empty_args) hinv19 h64 as ⟨v59, s20, hinv20, h_v59⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping he_v59 e_v59
          step as ⟨e_v60, he_v60⟩
          store_step with CtorSpec.eo__40purify.construct s20 e_v60 (by rw [he_v60]; exact empty_args) hinv20 h64 as ⟨v60, s21, hinv21, h_v60⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 dropping he_v60 e_v60
          step as ⟨e_v61, he_v61⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v61 (by rw [he_v61]; exact empty_args) hinv21 h64 as ⟨v61, s22, hinv22, h_v61⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 dropping he_v61 e_v61
          have h_ite_v68 := (show if_3_eo__24eo_5fprog_5fconcat_5flprop s22 a0 v7 ⦃ r s' => s'.Inv ∧ s22.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_3_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s22
            rcases Store.boolean_value_term h_a0 with ⟨hx_62, hbv_62⟩ | ⟨hx_62, hbv_62⟩ | ⟨hx_62, hbv_62⟩
            · ite_branch hbv_62
              step as ⟨e_v62, he_v62⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v62 (by rw [he_v62]; exact empty_args) hinv22 h64 as ⟨v62, s23, hinv23, h_v62⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 dropping he_v62 e_v62
              step as ⟨e_v63, he_v63⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s23 e_v63 (by rw [he_v63]; exact empty_args) hinv23 h64 as ⟨v63, s24, hinv24, h_v63⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 h_v62 dropping he_v63 e_v63
              step as ⟨e_v64, he_v64⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s24 e_v64 (by rw [he_v64]; rfl) h_v63 h_v7 hinv24 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v64, s25, hinv25, h_v64⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 h_v62 dropping h_v63 he_v64 e_v64 v63
              step as ⟨e_v65, he_v65⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s25 e_v65 (by rw [he_v65]; rfl) h_v62 h_v64 hinv25 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v65, s26, hinv26, h_v65⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 dropping h_v62 h_v64 he_v65 e_v65 v62 v64
              ite_done hinv26 hG with (eo_ite_true_rep _ hx_62 h_v65)
            · ite_branch hbv_62
              step as ⟨e_v66, he_v66⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v66 (by rw [he_v66]; exact empty_args) hinv22 h64 as ⟨v66, s23, hinv23, h_v66⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 dropping he_v66 e_v66
              step as ⟨e_v67, he_v67⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s23 e_v67 (by rw [he_v67]; rfl) h_v66 h_v7 hinv23 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v67, s24, hinv24, h_v67⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 dropping h_v66 he_v67 e_v67 v66
              ite_done hinv24 hG with (eo_ite_false_rep _ hx_62 h_v67)
            · ite_branch hbv_62
              ite_stuck hinv22 hG with hx_62)
          store_step with h_ite_v68 as ⟨v68, s23, hinv23, h_v68⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 dropping h_ite_v68
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s23 0#u32 (0) (by scalar_tac) hinv23 h64 as ⟨v69, s24, hinv24, h_v69⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v61 h_v68 dropping
          step as ⟨e_v70, he_v70⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s24 e_v70 (by rw [he_v70]; rfl) h_v61 h_v68 h_v69 hinv24 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v70, s25, hinv25, h_v70⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 dropping h_v61 h_v68 h_v69 he_v70 e_v70 v61 v68 v69
          step as ⟨e_v71, he_v71⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s25 e_v71 (by rw [he_v71]; exact empty_args) hinv25 h64 as ⟨v71, s26, hinv26, h_v71⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 dropping he_v71 e_v71
          have h_ite_v78 := (show if_4_eo__24eo_5fprog_5fconcat_5flprop s26 a0 v4 ⦃ r s' => s'.Inv ∧ s26.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_4_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s26
            rcases Store.boolean_value_term h_a0 with ⟨hx_72, hbv_72⟩ | ⟨hx_72, hbv_72⟩ | ⟨hx_72, hbv_72⟩
            · ite_branch hbv_72
              step as ⟨e_v72, he_v72⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s26 e_v72 (by rw [he_v72]; exact empty_args) hinv26 h64 as ⟨v72, s27, hinv27, h_v72⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 dropping he_v72 e_v72
              step as ⟨e_v73, he_v73⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v73 (by rw [he_v73]; exact empty_args) hinv27 h64 as ⟨v73, s28, hinv28, h_v73⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 h_v72 dropping he_v73 e_v73
              step as ⟨e_v74, he_v74⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s28 e_v74 (by rw [he_v74]; rfl) h_v73 h_v4 hinv28 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v74, s29, hinv29, h_v74⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 h_v72 dropping h_v73 he_v74 e_v74 v73
              step as ⟨e_v75, he_v75⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s29 e_v75 (by rw [he_v75]; rfl) h_v72 h_v74 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v75, s30, hinv30, h_v75⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 dropping h_v72 h_v74 he_v75 e_v75 v72 v74
              ite_done hinv30 hG with (eo_ite_true_rep _ hx_72 h_v75)
            · ite_branch hbv_72
              step as ⟨e_v76, he_v76⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s26 e_v76 (by rw [he_v76]; exact empty_args) hinv26 h64 as ⟨v76, s27, hinv27, h_v76⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 dropping he_v76 e_v76
              step as ⟨e_v77, he_v77⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s27 e_v77 (by rw [he_v77]; rfl) h_v76 h_v4 hinv27 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v77, s28, hinv28, h_v77⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 dropping h_v76 he_v77 e_v77 v76
              ite_done hinv28 hG with (eo_ite_false_rep _ hx_72 h_v77)
            · ite_branch hbv_72
              ite_stuck hinv26 hG with hx_72)
          store_step with h_ite_v78 as ⟨v78, s27, hinv27, h_v78⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 dropping h_ite_v78
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s27 0#u32 (0) (by scalar_tac) hinv27 h64 as ⟨v79, s28, hinv28, h_v79⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 h_v71 h_v78 dropping
          step as ⟨e_v80, he_v80⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s28 e_v80 (by rw [he_v80]; rfl) h_v71 h_v78 h_v79 hinv28 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v80, s29, hinv29, h_v80⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 h_v70 dropping h_v71 h_v78 h_v79 he_v80 e_v80 v71 v78 v79
          store_step with ih.eo__24str_5funify_5fsplit s29 v70 v80 a0 _ _ _ hinv29 h64 (hG.rem hrem) h_v70 h_v80 h_a0 as ⟨v81, s30, hinv30, h_v81⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 h_v60 dropping h_v70 h_v80 v70 v80
          store_step with Store.apply_mk_rep s30 v60 v81 _ _ hinv30 h64 h_v60 h_v81 as ⟨v82, s31, hinv31, h_v82⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v59 dropping h_v60 h_v81 v60 v81
          store_step with Store.apply_mk_rep s31 v59 v82 _ _ hinv31 h64 h_v59 h_v82 as ⟨v83, s32, hinv32, h_v83⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping h_v59 h_v82 v59 v82
          step as ⟨e_v84, he_v84⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s32 e_v84 (by rw [he_v84]; exact empty_args) hinv32 h64 as ⟨v84, s33, hinv33, h_v84⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 dropping he_v84 e_v84
          step as ⟨e_v85, he_v85⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v85 (by rw [he_v85]; exact empty_args) hinv33 h64 as ⟨v85, s34, hinv34, h_v85⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 dropping he_v85 e_v85
          have h_ite_v92 := (show if_5_eo__24eo_5fprog_5fconcat_5flprop s34 a0 v4 ⦃ r s' => s'.Inv ∧ s34.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_5_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s34
            rcases Store.boolean_value_term h_a0 with ⟨hx_86, hbv_86⟩ | ⟨hx_86, hbv_86⟩ | ⟨hx_86, hbv_86⟩
            · ite_branch hbv_86
              step as ⟨e_v86, he_v86⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v86 (by rw [he_v86]; exact empty_args) hinv34 h64 as ⟨v86, s35, hinv35, h_v86⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 dropping he_v86 e_v86
              step as ⟨e_v87, he_v87⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v87 (by rw [he_v87]; exact empty_args) hinv35 h64 as ⟨v87, s36, hinv36, h_v87⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 h_v86 dropping he_v87 e_v87
              step as ⟨e_v88, he_v88⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s36 e_v88 (by rw [he_v88]; rfl) h_v87 h_v4 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v88, s37, hinv37, h_v88⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 h_v86 dropping h_v87 he_v88 e_v88 v87
              step as ⟨e_v89, he_v89⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s37 e_v89 (by rw [he_v89]; rfl) h_v86 h_v88 hinv37 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v89, s38, hinv38, h_v89⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 dropping h_v86 h_v88 he_v89 e_v89 v86 v88
              ite_done hinv38 hG with (eo_ite_true_rep _ hx_86 h_v89)
            · ite_branch hbv_86
              step as ⟨e_v90, he_v90⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v90 (by rw [he_v90]; exact empty_args) hinv34 h64 as ⟨v90, s35, hinv35, h_v90⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 dropping he_v90 e_v90
              step as ⟨e_v91, he_v91⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s35 e_v91 (by rw [he_v91]; rfl) h_v90 h_v4 hinv35 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v91, s36, hinv36, h_v91⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 dropping h_v90 he_v91 e_v91 v90
              ite_done hinv36 hG with (eo_ite_false_rep _ hx_86 h_v91)
            · ite_branch hbv_86
              ite_stuck hinv34 hG with hx_86)
          store_step with h_ite_v92 as ⟨v92, s35, hinv35, h_v92⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 dropping h_ite_v92
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v93, s36, hinv36, h_v93⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 h_v85 h_v92 dropping
          step as ⟨e_v94, he_v94⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s36 e_v94 (by rw [he_v94]; rfl) h_v85 h_v92 h_v93 hinv36 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v94, s37, hinv37, h_v94⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v84 dropping h_v85 h_v92 h_v93 he_v94 e_v94 v85 v92 v93
          store_step with Store.apply_mk_rep s37 v84 v94 _ _ hinv37 h64 h_v84 h_v94 as ⟨v95, s38, hinv38, h_v95⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 dropping h_v84 h_v94 v84 v94
          step as ⟨e_v96, he_v96⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s38 e_v96 (by rw [he_v96]; exact empty_args) hinv38 h64 as ⟨v96, s39, hinv39, h_v96⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 dropping he_v96 e_v96
          step as ⟨e_v97, he_v97⟩
          store_step with CtorSpec.eo__40purify.construct s39 e_v97 (by rw [he_v97]; exact empty_args) hinv39 h64 as ⟨v97, s40, hinv40, h_v97⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 dropping he_v97 e_v97
          step as ⟨e_v98, he_v98⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v98 (by rw [he_v98]; exact empty_args) hinv40 h64 as ⟨v98, s41, hinv41, h_v98⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 dropping he_v98 e_v98
          have h_ite_v105 := (show if_6_eo__24eo_5fprog_5fconcat_5flprop s41 a0 v7 ⦃ r s' => s'.Inv ∧ s41.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_6_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s41
            rcases Store.boolean_value_term h_a0 with ⟨hx_99, hbv_99⟩ | ⟨hx_99, hbv_99⟩ | ⟨hx_99, hbv_99⟩
            · ite_branch hbv_99
              step as ⟨e_v99, he_v99⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v99 (by rw [he_v99]; exact empty_args) hinv41 h64 as ⟨v99, s42, hinv42, h_v99⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 dropping he_v99 e_v99
              step as ⟨e_v100, he_v100⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v100 (by rw [he_v100]; exact empty_args) hinv42 h64 as ⟨v100, s43, hinv43, h_v100⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 h_v99 dropping he_v100 e_v100
              step as ⟨e_v101, he_v101⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s43 e_v101 (by rw [he_v101]; rfl) h_v100 h_v7 hinv43 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v101, s44, hinv44, h_v101⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 h_v99 dropping h_v100 he_v101 e_v101 v100
              step as ⟨e_v102, he_v102⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s44 e_v102 (by rw [he_v102]; rfl) h_v99 h_v101 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v102, s45, hinv45, h_v102⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 dropping h_v101 h_v99 he_v102 e_v102 v101 v99
              ite_done hinv45 hG with (eo_ite_true_rep _ hx_99 h_v102)
            · ite_branch hbv_99
              step as ⟨e_v103, he_v103⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v103 (by rw [he_v103]; exact empty_args) hinv41 h64 as ⟨v103, s42, hinv42, h_v103⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 dropping he_v103 e_v103
              step as ⟨e_v104, he_v104⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s42 e_v104 (by rw [he_v104]; rfl) h_v103 h_v7 hinv42 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v104, s43, hinv43, h_v104⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 dropping h_v103 he_v104 e_v104 v103
              ite_done hinv43 hG with (eo_ite_false_rep _ hx_99 h_v104)
            · ite_branch hbv_99
              ite_stuck hinv41 hG with hx_99)
          store_step with h_ite_v105 as ⟨v105, s42, hinv42, h_v105⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 dropping h_ite_v105
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s42 0#u32 (0) (by scalar_tac) hinv42 h64 as ⟨v106, s43, hinv43, h_v106⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v98 h_v105 dropping
          step as ⟨e_v107, he_v107⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s43 e_v107 (by rw [he_v107]; rfl) h_v98 h_v105 h_v106 hinv43 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v107, s44, hinv44, h_v107⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 dropping h_v105 h_v106 h_v98 he_v107 e_v107 v105 v106 v98
          step as ⟨e_v108, he_v108⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v108 (by rw [he_v108]; exact empty_args) hinv44 h64 as ⟨v108, s45, hinv45, h_v108⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 dropping he_v108 e_v108
          have h_ite_v115 := (show if_7_eo__24eo_5fprog_5fconcat_5flprop s45 a0 v4 ⦃ r s' => s'.Inv ∧ s45.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_7_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s45
            rcases Store.boolean_value_term h_a0 with ⟨hx_109, hbv_109⟩ | ⟨hx_109, hbv_109⟩ | ⟨hx_109, hbv_109⟩
            · ite_branch hbv_109
              step as ⟨e_v109, he_v109⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s45 e_v109 (by rw [he_v109]; exact empty_args) hinv45 h64 as ⟨v109, s46, hinv46, h_v109⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 dropping he_v109 e_v109
              step as ⟨e_v110, he_v110⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s46 e_v110 (by rw [he_v110]; exact empty_args) hinv46 h64 as ⟨v110, s47, hinv47, h_v110⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 h_v109 dropping he_v110 e_v110
              step as ⟨e_v111, he_v111⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s47 e_v111 (by rw [he_v111]; rfl) h_v110 h_v4 hinv47 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v111, s48, hinv48, h_v111⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 h_v109 dropping h_v110 he_v111 e_v111 v110
              step as ⟨e_v112, he_v112⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s48 e_v112 (by rw [he_v112]; rfl) h_v109 h_v111 hinv48 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v112, s49, hinv49, h_v112⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 dropping h_v109 h_v111 he_v112 e_v112 v109 v111
              ite_done hinv49 hG with (eo_ite_true_rep _ hx_109 h_v112)
            · ite_branch hbv_109
              step as ⟨e_v113, he_v113⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s45 e_v113 (by rw [he_v113]; exact empty_args) hinv45 h64 as ⟨v113, s46, hinv46, h_v113⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 dropping he_v113 e_v113
              step as ⟨e_v114, he_v114⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s46 e_v114 (by rw [he_v114]; rfl) h_v113 h_v4 hinv46 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v114, s47, hinv47, h_v114⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 dropping h_v113 he_v114 e_v114 v113
              ite_done hinv47 hG with (eo_ite_false_rep _ hx_109 h_v114)
            · ite_branch hbv_109
              ite_stuck hinv45 hG with hx_109)
          store_step with h_ite_v115 as ⟨v115, s46, hinv46, h_v115⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 dropping h_ite_v115
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s46 0#u32 (0) (by scalar_tac) hinv46 h64 as ⟨v116, s47, hinv47, h_v116⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 h_v108 h_v115 dropping
          step as ⟨e_v117, he_v117⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s47 e_v117 (by rw [he_v117]; rfl) h_v108 h_v115 h_v116 hinv47 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v117, s48, hinv48, h_v117⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 h_v107 dropping h_v108 h_v115 h_v116 he_v117 e_v117 v108 v115 v116
          store_step with ih.eo__24str_5funify_5fsplit s48 v107 v117 a0 _ _ _ hinv48 h64 (hG.rem hrem) h_v107 h_v117 h_a0 as ⟨v118, s49, hinv49, h_v118⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 h_v97 dropping h_v107 h_v117 v107 v117
          store_step with Store.apply_mk_rep s49 v97 v118 _ _ hinv49 h64 h_v97 h_v118 as ⟨v119, s50, hinv50, h_v119⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 dropping h_v118 h_v97 v118 v97
          store_step with ih.eo__24eo_5ftypeof s50 v119 _ hinv50 h64 (hG.rem hrem) h_v119 as ⟨v120, s51, hinv51, h_v120⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 h_v96 dropping h_v119 v119
          store_step with ih.eo__24eo_5fnil s51 v96 v120 _ _ hinv51 h64 (hG.rem hrem) h_v96 h_v120 as ⟨v121, s52, hinv52, h_v121⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 h_v95 dropping h_v120 h_v96 v120 v96
          store_step with Store.apply_mk_rep s52 v95 v121 _ _ hinv52 h64 h_v95 h_v121 as ⟨v122, s53, hinv53, h_v122⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v83 dropping h_v121 h_v95 v121 v95
          store_step with Store.apply_mk_rep s53 v83 v122 _ _ hinv53 h64 h_v83 h_v122 as ⟨v123, s54, hinv54, h_v123⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping h_v122 h_v83 v122 v83
          ite_done hinv54 hG with (eo_ite_true_rep _ hx_59 h_v123)
        · ite_branch hbv_59
          step as ⟨e_v124, he_v124⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v124 (by rw [he_v124]; exact empty_args) hinv19 h64 as ⟨v124, s20, hinv20, h_v124⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping he_v124 e_v124
          step as ⟨e_v125, he_v125⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s20 e_v125 (by rw [he_v125]; exact empty_args) hinv20 h64 as ⟨v125, s21, hinv21, h_v125⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 dropping he_v125 e_v125
          have h_ite_v132 := (show if_8_eo__24eo_5fprog_5fconcat_5flprop s21 a0 v4 ⦃ r s' => s'.Inv ∧ s21.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_8_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s21
            rcases Store.boolean_value_term h_a0 with ⟨hx_126, hbv_126⟩ | ⟨hx_126, hbv_126⟩ | ⟨hx_126, hbv_126⟩
            · ite_branch hbv_126
              step as ⟨e_v126, he_v126⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v126 (by rw [he_v126]; exact empty_args) hinv21 h64 as ⟨v126, s22, hinv22, h_v126⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 dropping he_v126 e_v126
              step as ⟨e_v127, he_v127⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v127 (by rw [he_v127]; exact empty_args) hinv22 h64 as ⟨v127, s23, hinv23, h_v127⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 h_v126 dropping he_v127 e_v127
              step as ⟨e_v128, he_v128⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s23 e_v128 (by rw [he_v128]; rfl) h_v127 h_v4 hinv23 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v128, s24, hinv24, h_v128⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 h_v126 dropping h_v127 he_v128 e_v128 v127
              step as ⟨e_v129, he_v129⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s24 e_v129 (by rw [he_v129]; rfl) h_v126 h_v128 hinv24 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v129, s25, hinv25, h_v129⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 dropping h_v126 h_v128 he_v129 e_v129 v126 v128
              ite_done hinv25 hG with (eo_ite_true_rep _ hx_126 h_v129)
            · ite_branch hbv_126
              step as ⟨e_v130, he_v130⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v130 (by rw [he_v130]; exact empty_args) hinv21 h64 as ⟨v130, s22, hinv22, h_v130⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 dropping he_v130 e_v130
              step as ⟨e_v131, he_v131⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s22 e_v131 (by rw [he_v131]; rfl) h_v130 h_v4 hinv22 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v131, s23, hinv23, h_v131⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 dropping h_v130 he_v131 e_v131 v130
              ite_done hinv23 hG with (eo_ite_false_rep _ hx_126 h_v131)
            · ite_branch hbv_126
              ite_stuck hinv21 hG with hx_126)
          store_step with h_ite_v132 as ⟨v132, s22, hinv22, h_v132⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 dropping h_ite_v132
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s22 0#u32 (0) (by scalar_tac) hinv22 h64 as ⟨v133, s23, hinv23, h_v133⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 h_v125 h_v132 dropping
          step as ⟨e_v134, he_v134⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s23 e_v134 (by rw [he_v134]; rfl) h_v125 h_v132 h_v133 hinv23 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v134, s24, hinv24, h_v134⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v124 dropping h_v125 h_v132 h_v133 he_v134 e_v134 v125 v132 v133
          store_step with Store.apply_mk_rep s24 v124 v134 _ _ hinv24 h64 h_v124 h_v134 as ⟨v135, s25, hinv25, h_v135⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping h_v124 h_v134 v124 v134
          step as ⟨e_v136, he_v136⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s25 e_v136 (by rw [he_v136]; exact empty_args) hinv25 h64 as ⟨v136, s26, hinv26, h_v136⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 dropping he_v136 e_v136
          step as ⟨e_v137, he_v137⟩
          store_step with CtorSpec.eo__40purify.construct s26 e_v137 (by rw [he_v137]; exact empty_args) hinv26 h64 as ⟨v137, s27, hinv27, h_v137⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 dropping he_v137 e_v137
          step as ⟨e_v138, he_v138⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v138 (by rw [he_v138]; exact empty_args) hinv27 h64 as ⟨v138, s28, hinv28, h_v138⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 dropping he_v138 e_v138
          have h_ite_v145 := (show if_9_eo__24eo_5fprog_5fconcat_5flprop s28 a0 v7 ⦃ r s' => s'.Inv ∧ s28.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_9_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s28
            rcases Store.boolean_value_term h_a0 with ⟨hx_139, hbv_139⟩ | ⟨hx_139, hbv_139⟩ | ⟨hx_139, hbv_139⟩
            · ite_branch hbv_139
              step as ⟨e_v139, he_v139⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v139 (by rw [he_v139]; exact empty_args) hinv28 h64 as ⟨v139, s29, hinv29, h_v139⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 dropping he_v139 e_v139
              step as ⟨e_v140, he_v140⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s29 e_v140 (by rw [he_v140]; exact empty_args) hinv29 h64 as ⟨v140, s30, hinv30, h_v140⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 h_v139 dropping he_v140 e_v140
              step as ⟨e_v141, he_v141⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s30 e_v141 (by rw [he_v141]; rfl) h_v140 h_v7 hinv30 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v141, s31, hinv31, h_v141⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 h_v139 dropping h_v140 he_v141 e_v141 v140
              step as ⟨e_v142, he_v142⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s31 e_v142 (by rw [he_v142]; rfl) h_v139 h_v141 hinv31 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v142, s32, hinv32, h_v142⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 dropping h_v139 h_v141 he_v142 e_v142 v139 v141
              ite_done hinv32 hG with (eo_ite_true_rep _ hx_139 h_v142)
            · ite_branch hbv_139
              step as ⟨e_v143, he_v143⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v143 (by rw [he_v143]; exact empty_args) hinv28 h64 as ⟨v143, s29, hinv29, h_v143⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 dropping he_v143 e_v143
              step as ⟨e_v144, he_v144⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s29 e_v144 (by rw [he_v144]; rfl) h_v143 h_v7 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v144, s30, hinv30, h_v144⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 dropping h_v143 he_v144 e_v144 v143
              ite_done hinv30 hG with (eo_ite_false_rep _ hx_139 h_v144)
            · ite_branch hbv_139
              ite_stuck hinv28 hG with hx_139)
          store_step with h_ite_v145 as ⟨v145, s29, hinv29, h_v145⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 dropping h_ite_v145
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s29 0#u32 (0) (by scalar_tac) hinv29 h64 as ⟨v146, s30, hinv30, h_v146⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v138 h_v145 dropping
          step as ⟨e_v147, he_v147⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s30 e_v147 (by rw [he_v147]; rfl) h_v138 h_v145 h_v146 hinv30 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v147, s31, hinv31, h_v147⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 dropping h_v138 h_v145 h_v146 he_v147 e_v147 v138 v145 v146
          step as ⟨e_v148, he_v148⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v148 (by rw [he_v148]; exact empty_args) hinv31 h64 as ⟨v148, s32, hinv32, h_v148⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 dropping he_v148 e_v148
          have h_ite_v155 := (show if_10_eo__24eo_5fprog_5fconcat_5flprop s32 a0 v4 ⦃ r s' => s'.Inv ∧ s32.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_10_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s32
            rcases Store.boolean_value_term h_a0 with ⟨hx_149, hbv_149⟩ | ⟨hx_149, hbv_149⟩ | ⟨hx_149, hbv_149⟩
            · ite_branch hbv_149
              step as ⟨e_v149, he_v149⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s32 e_v149 (by rw [he_v149]; exact empty_args) hinv32 h64 as ⟨v149, s33, hinv33, h_v149⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 dropping he_v149 e_v149
              step as ⟨e_v150, he_v150⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s33 e_v150 (by rw [he_v150]; exact empty_args) hinv33 h64 as ⟨v150, s34, hinv34, h_v150⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 h_v149 dropping he_v150 e_v150
              step as ⟨e_v151, he_v151⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s34 e_v151 (by rw [he_v151]; rfl) h_v150 h_v4 hinv34 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v151, s35, hinv35, h_v151⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 h_v149 dropping h_v150 he_v151 e_v151 v150
              step as ⟨e_v152, he_v152⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s35 e_v152 (by rw [he_v152]; rfl) h_v149 h_v151 hinv35 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v152, s36, hinv36, h_v152⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 dropping h_v149 h_v151 he_v152 e_v152 v149 v151
              ite_done hinv36 hG with (eo_ite_true_rep _ hx_149 h_v152)
            · ite_branch hbv_149
              step as ⟨e_v153, he_v153⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s32 e_v153 (by rw [he_v153]; exact empty_args) hinv32 h64 as ⟨v153, s33, hinv33, h_v153⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 dropping he_v153 e_v153
              step as ⟨e_v154, he_v154⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s33 e_v154 (by rw [he_v154]; rfl) h_v153 h_v4 hinv33 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v154, s34, hinv34, h_v154⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 dropping h_v153 he_v154 e_v154 v153
              ite_done hinv34 hG with (eo_ite_false_rep _ hx_149 h_v154)
            · ite_branch hbv_149
              ite_stuck hinv32 hG with hx_149)
          store_step with h_ite_v155 as ⟨v155, s33, hinv33, h_v155⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 dropping h_ite_v155
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s33 0#u32 (0) (by scalar_tac) hinv33 h64 as ⟨v156, s34, hinv34, h_v156⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 h_v148 h_v155 dropping
          step as ⟨e_v157, he_v157⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s34 e_v157 (by rw [he_v157]; rfl) h_v148 h_v155 h_v156 hinv34 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v157, s35, hinv35, h_v157⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 h_v147 dropping h_v148 h_v155 h_v156 he_v157 e_v157 v148 v155 v156
          store_step with ih.eo__24str_5funify_5fsplit s35 v147 v157 a0 _ _ _ hinv35 h64 (hG.rem hrem) h_v147 h_v157 h_a0 as ⟨v158, s36, hinv36, h_v158⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 h_v137 dropping h_v147 h_v157 v147 v157
          store_step with Store.apply_mk_rep s36 v137 v158 _ _ hinv36 h64 h_v137 h_v158 as ⟨v159, s37, hinv37, h_v159⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v136 dropping h_v137 h_v158 v137 v158
          store_step with Store.apply_mk_rep s37 v136 v159 _ _ hinv37 h64 h_v136 h_v159 as ⟨v160, s38, hinv38, h_v160⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 dropping h_v136 h_v159 v136 v159
          step as ⟨e_v161, he_v161⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s38 e_v161 (by rw [he_v161]; exact empty_args) hinv38 h64 as ⟨v161, s39, hinv39, h_v161⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 dropping he_v161 e_v161
          step as ⟨e_v162, he_v162⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s39 e_v162 (by rw [he_v162]; exact empty_args) hinv39 h64 as ⟨v162, s40, hinv40, h_v162⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 dropping he_v162 e_v162
          have h_ite_v169 := (show if_11_eo__24eo_5fprog_5fconcat_5flprop s40 a0 v4 ⦃ r s' => s'.Inv ∧ s40.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold if_11_eo__24eo_5fprog_5fconcat_5flprop
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s40
            rcases Store.boolean_value_term h_a0 with ⟨hx_163, hbv_163⟩ | ⟨hx_163, hbv_163⟩ | ⟨hx_163, hbv_163⟩
            · ite_branch hbv_163
              step as ⟨e_v163, he_v163⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v163 (by rw [he_v163]; exact empty_args) hinv40 h64 as ⟨v163, s41, hinv41, h_v163⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 dropping he_v163 e_v163
              step as ⟨e_v164, he_v164⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s41 e_v164 (by rw [he_v164]; exact empty_args) hinv41 h64 as ⟨v164, s42, hinv42, h_v164⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 h_v163 dropping he_v164 e_v164
              step as ⟨e_v165, he_v165⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s42 e_v165 (by rw [he_v165]; rfl) h_v164 h_v4 hinv42 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v165, s43, hinv43, h_v165⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 h_v163 dropping h_v164 he_v165 e_v165 v164
              step as ⟨e_v166, he_v166⟩
              store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s43 e_v166 (by rw [he_v166]; rfl) h_v163 h_v165 hinv43 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v166, s44, hinv44, h_v166⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 dropping h_v163 h_v165 he_v166 e_v166 v163 v165
              ite_done hinv44 hG with (eo_ite_true_rep _ hx_163 h_v166)
            · ite_branch hbv_163
              step as ⟨e_v167, he_v167⟩
              store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v167 (by rw [he_v167]; exact empty_args) hinv40 h64 as ⟨v167, s41, hinv41, h_v167⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 dropping he_v167 e_v167
              step as ⟨e_v168, he_v168⟩
              store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s41 e_v168 (by rw [he_v168]; rfl) h_v167 h_v4 hinv41 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v168, s42, hinv42, h_v168⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 dropping h_v167 he_v168 e_v168 v167
              ite_done hinv42 hG with (eo_ite_false_rep _ hx_163 h_v168)
            · ite_branch hbv_163
              ite_stuck hinv40 hG with hx_163)
          store_step with h_ite_v169 as ⟨v169, s41, hinv41, h_v169⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 dropping h_ite_v169
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s41 0#u32 (0) (by scalar_tac) hinv41 h64 as ⟨v170, s42, hinv42, h_v170⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 h_v162 h_v169 dropping
          step as ⟨e_v171, he_v171⟩
          store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s42 e_v171 (by rw [he_v171]; rfl) h_v162 h_v169 h_v170 hinv42 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v171, s43, hinv43, h_v171⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 dropping h_v162 h_v169 h_v170 he_v171 e_v171 v162 v169 v170
          store_step with ih.eo__24eo_5ftypeof s43 v171 _ hinv43 h64 (hG.rem hrem) h_v171 as ⟨v172, s44, hinv44, h_v172⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 h_v161 dropping h_v171 v171
          store_step with ih.eo__24eo_5fnil s44 v161 v172 _ _ hinv44 h64 (hG.rem hrem) h_v161 h_v172 as ⟨v173, s45, hinv45, h_v173⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 h_v160 dropping h_v161 h_v172 v161 v172
          store_step with Store.apply_mk_rep s45 v160 v173 _ _ hinv45 h64 h_v160 h_v173 as ⟨v174, s46, hinv46, h_v174⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 h_v135 dropping h_v160 h_v173 v160 v173
          store_step with Store.apply_mk_rep s46 v135 v174 _ _ hinv46 h64 h_v135 h_v174 as ⟨v175, s47, hinv47, h_v175⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping h_v135 h_v174 v135 v174
          ite_done hinv47 hG with (eo_ite_false_rep _ hx_59 h_v175)
        · ite_branch hbv_59
          ite_stuck hinv19 hG with hx_59)
      store_step with h_ite_v176 as ⟨v176, s20, hinv20, h_v176⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 h_v58 dropping h_ite_v176 hinv19 s19
      store_step with Store.apply_mk_rep s20 v58 v176 _ _ hinv20 h64 h_v58 h_v176 as ⟨v177, s21, hinv21, h_v177⟩ growing hG carrying h_a0 h_v4 h_v7 h_v46 dropping h_v176 h_v58 hinv20 s20 v176 v58
      store_step with Store.apply_mk_rep s21 v46 v177 _ _ hinv21 h64 h_v46 h_v177 as ⟨v178, s22, hinv22, h_v178⟩ growing hG carrying h_a0 h_v4 h_v7 dropping h_v177 h_v46 hinv21 s21 v177 v46
      step as ⟨e_v179, he_v179⟩
      store_step with CtorSpec.eo_and.construct s22 e_v179 (by rw [he_v179]; exact empty_args) hinv22 h64 as ⟨v179, s23, hinv23, h_v179⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 dropping he_v179 hinv22 e_v179 s22
      step as ⟨e_v180, he_v180⟩
      store_step with CtorSpec.eo_not.construct s23 e_v180 (by rw [he_v180]; exact empty_args) hinv23 h64 as ⟨v180, s24, hinv24, h_v180⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 dropping he_v180 hinv23 e_v180 s23
      step as ⟨e_v181, he_v181⟩
      store_step with CtorSpec.eo__3d.construct s24 e_v181 (by rw [he_v181]; exact empty_args) hinv24 h64 as ⟨v181, s25, hinv25, h_v181⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 dropping he_v181 hinv24 e_v181 s24
      step as ⟨e_v182, he_v182⟩
      store_step with CtorSpec.eo__40purify.construct s25 e_v182 (by rw [he_v182]; exact empty_args) hinv25 h64 as ⟨v182, s26, hinv26, h_v182⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 dropping he_v182 hinv25 e_v182 s25
      step as ⟨e_v183, he_v183⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s26 e_v183 (by rw [he_v183]; exact empty_args) hinv26 h64 as ⟨v183, s27, hinv27, h_v183⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 dropping he_v183 hinv26 e_v183 s26
      have h_ite_v190 := (show if_17_eo__24eo_5fprog_5fconcat_5flprop s27 a0 v7 ⦃ r s' => s'.Inv ∧ s27.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_17_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s27
        rcases Store.boolean_value_term h_a0 with ⟨hx_184, hbv_184⟩ | ⟨hx_184, hbv_184⟩ | ⟨hx_184, hbv_184⟩
        · ite_branch hbv_184
          step as ⟨e_v184, he_v184⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v184 (by rw [he_v184]; exact empty_args) hinv27 h64 as ⟨v184, s28, hinv28, h_v184⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 dropping he_v184 e_v184
          step as ⟨e_v185, he_v185⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v185 (by rw [he_v185]; exact empty_args) hinv28 h64 as ⟨v185, s29, hinv29, h_v185⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 h_v184 dropping he_v185 e_v185
          step as ⟨e_v186, he_v186⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s29 e_v186 (by rw [he_v186]; rfl) h_v185 h_v7 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v186, s30, hinv30, h_v186⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 h_v184 dropping h_v185 he_v186 e_v186 v185
          step as ⟨e_v187, he_v187⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s30 e_v187 (by rw [he_v187]; rfl) h_v184 h_v186 hinv30 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v187, s31, hinv31, h_v187⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 dropping h_v184 h_v186 he_v187 e_v187 v184 v186
          ite_done hinv31 hG with (eo_ite_true_rep _ hx_184 h_v187)
        · ite_branch hbv_184
          step as ⟨e_v188, he_v188⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v188 (by rw [he_v188]; exact empty_args) hinv27 h64 as ⟨v188, s28, hinv28, h_v188⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 dropping he_v188 e_v188
          step as ⟨e_v189, he_v189⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s28 e_v189 (by rw [he_v189]; rfl) h_v188 h_v7 hinv28 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v189, s29, hinv29, h_v189⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 dropping h_v188 he_v189 e_v189 v188
          ite_done hinv29 hG with (eo_ite_false_rep _ hx_184 h_v189)
        · ite_branch hbv_184
          ite_stuck hinv27 hG with hx_184)
      store_step with h_ite_v190 as ⟨v190, s28, hinv28, h_v190⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 dropping h_ite_v190 hinv27 s27
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s28 0#u32 (0) (by scalar_tac) hinv28 h64 as ⟨v191, s29, hinv29, h_v191⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v183 h_v190 dropping hinv28 s28
      step as ⟨e_v192, he_v192⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s29 e_v192 (by rw [he_v192]; rfl) h_v183 h_v190 h_v191 hinv29 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v192, s30, hinv30, h_v192⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 dropping h_v183 h_v190 h_v191 he_v192 hinv29 e_v192 s29 v183 v190 v191
      step as ⟨e_v193, he_v193⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s30 e_v193 (by rw [he_v193]; exact empty_args) hinv30 h64 as ⟨v193, s31, hinv31, h_v193⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 dropping he_v193 hinv30 e_v193 s30
      have h_ite_v200 := (show if_18_eo__24eo_5fprog_5fconcat_5flprop s31 a0 v4 ⦃ r s' => s'.Inv ∧ s31.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_18_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s31
        rcases Store.boolean_value_term h_a0 with ⟨hx_194, hbv_194⟩ | ⟨hx_194, hbv_194⟩ | ⟨hx_194, hbv_194⟩
        · ite_branch hbv_194
          step as ⟨e_v194, he_v194⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v194 (by rw [he_v194]; exact empty_args) hinv31 h64 as ⟨v194, s32, hinv32, h_v194⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 dropping he_v194 e_v194
          step as ⟨e_v195, he_v195⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s32 e_v195 (by rw [he_v195]; exact empty_args) hinv32 h64 as ⟨v195, s33, hinv33, h_v195⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 h_v194 dropping he_v195 e_v195
          step as ⟨e_v196, he_v196⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s33 e_v196 (by rw [he_v196]; rfl) h_v195 h_v4 hinv33 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v196, s34, hinv34, h_v196⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 h_v194 dropping h_v195 he_v196 e_v196 v195
          step as ⟨e_v197, he_v197⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s34 e_v197 (by rw [he_v197]; rfl) h_v194 h_v196 hinv34 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v197, s35, hinv35, h_v197⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 dropping h_v194 h_v196 he_v197 e_v197 v194 v196
          ite_done hinv35 hG with (eo_ite_true_rep _ hx_194 h_v197)
        · ite_branch hbv_194
          step as ⟨e_v198, he_v198⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v198 (by rw [he_v198]; exact empty_args) hinv31 h64 as ⟨v198, s32, hinv32, h_v198⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 dropping he_v198 e_v198
          step as ⟨e_v199, he_v199⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s32 e_v199 (by rw [he_v199]; rfl) h_v198 h_v4 hinv32 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v199, s33, hinv33, h_v199⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 dropping h_v198 he_v199 e_v199 v198
          ite_done hinv33 hG with (eo_ite_false_rep _ hx_194 h_v199)
        · ite_branch hbv_194
          ite_stuck hinv31 hG with hx_194)
      store_step with h_ite_v200 as ⟨v200, s32, hinv32, h_v200⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 dropping h_ite_v200 hinv31 s31
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v201, s33, hinv33, h_v201⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 h_v193 h_v200 dropping hinv32 s32
      step as ⟨e_v202, he_v202⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s33 e_v202 (by rw [he_v202]; rfl) h_v193 h_v200 h_v201 hinv33 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v202, s34, hinv34, h_v202⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 h_v192 dropping h_v193 h_v200 h_v201 he_v202 hinv33 e_v202 s33 v193 v200 v201
      store_step with ih.eo__24str_5funify_5fsplit s34 v192 v202 a0 _ _ _ hinv34 h64 (hG.rem hrem) h_v192 h_v202 h_a0 as ⟨v203, s35, hinv35, h_v203⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 h_v182 dropping h_v192 h_v202 hinv34 s34 v192 v202
      store_step with Store.apply_mk_rep s35 v182 v203 _ _ hinv35 h64 h_v182 h_v203 as ⟨v204, s36, hinv36, h_v204⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v181 dropping h_v182 h_v203 hinv35 s35 v182 v203
      store_step with Store.apply_mk_rep s36 v181 v204 _ _ hinv36 h64 h_v181 h_v204 as ⟨v205, s37, hinv37, h_v205⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 dropping h_v181 h_v204 hinv36 s36 v181 v204
      step as ⟨e_v206, he_v206⟩
      store_step with CtorSpec.eo__40purify.construct s37 e_v206 (by rw [he_v206]; exact empty_args) hinv37 h64 as ⟨v206, s38, hinv38, h_v206⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 dropping he_v206 hinv37 e_v206 s37
      step as ⟨e_v207, he_v207⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s38 e_v207 (by rw [he_v207]; exact empty_args) hinv38 h64 as ⟨v207, s39, hinv39, h_v207⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 dropping he_v207 hinv38 e_v207 s38
      have h_ite_v214 := (show if_19_eo__24eo_5fprog_5fconcat_5flprop s39 a0 v7 ⦃ r s' => s'.Inv ∧ s39.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_19_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s39
        rcases Store.boolean_value_term h_a0 with ⟨hx_208, hbv_208⟩ | ⟨hx_208, hbv_208⟩ | ⟨hx_208, hbv_208⟩
        · ite_branch hbv_208
          step as ⟨e_v208, he_v208⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s39 e_v208 (by rw [he_v208]; exact empty_args) hinv39 h64 as ⟨v208, s40, hinv40, h_v208⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 dropping he_v208 e_v208
          step as ⟨e_v209, he_v209⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v209 (by rw [he_v209]; exact empty_args) hinv40 h64 as ⟨v209, s41, hinv41, h_v209⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 h_v208 dropping he_v209 e_v209
          step as ⟨e_v210, he_v210⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s41 e_v210 (by rw [he_v210]; rfl) h_v209 h_v7 hinv41 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v210, s42, hinv42, h_v210⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 h_v208 dropping h_v209 he_v210 e_v210 v209
          step as ⟨e_v211, he_v211⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s42 e_v211 (by rw [he_v211]; rfl) h_v208 h_v210 hinv42 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v211, s43, hinv43, h_v211⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 dropping h_v208 h_v210 he_v211 e_v211 v208 v210
          ite_done hinv43 hG with (eo_ite_true_rep _ hx_208 h_v211)
        · ite_branch hbv_208
          step as ⟨e_v212, he_v212⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s39 e_v212 (by rw [he_v212]; exact empty_args) hinv39 h64 as ⟨v212, s40, hinv40, h_v212⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 dropping he_v212 e_v212
          step as ⟨e_v213, he_v213⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s40 e_v213 (by rw [he_v213]; rfl) h_v212 h_v7 hinv40 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v213, s41, hinv41, h_v213⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 dropping h_v212 he_v213 e_v213 v212
          ite_done hinv41 hG with (eo_ite_false_rep _ hx_208 h_v213)
        · ite_branch hbv_208
          ite_stuck hinv39 hG with hx_208)
      store_step with h_ite_v214 as ⟨v214, s40, hinv40, h_v214⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 dropping h_ite_v214 hinv39 s39
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s40 0#u32 (0) (by scalar_tac) hinv40 h64 as ⟨v215, s41, hinv41, h_v215⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v207 h_v214 dropping hinv40 s40
      step as ⟨e_v216, he_v216⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s41 e_v216 (by rw [he_v216]; rfl) h_v207 h_v214 h_v215 hinv41 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v216, s42, hinv42, h_v216⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 dropping h_v207 h_v214 h_v215 he_v216 hinv41 e_v216 s41 v207 v214 v215
      step as ⟨e_v217, he_v217⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s42 e_v217 (by rw [he_v217]; exact empty_args) hinv42 h64 as ⟨v217, s43, hinv43, h_v217⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 dropping he_v217 hinv42 e_v217 s42
      have h_ite_v224 := (show if_20_eo__24eo_5fprog_5fconcat_5flprop s43 a0 v4 ⦃ r s' => s'.Inv ∧ s43.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_20_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s43
        rcases Store.boolean_value_term h_a0 with ⟨hx_218, hbv_218⟩ | ⟨hx_218, hbv_218⟩ | ⟨hx_218, hbv_218⟩
        · ite_branch hbv_218
          step as ⟨e_v218, he_v218⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v218 (by rw [he_v218]; exact empty_args) hinv43 h64 as ⟨v218, s44, hinv44, h_v218⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 dropping he_v218 e_v218
          step as ⟨e_v219, he_v219⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s44 e_v219 (by rw [he_v219]; exact empty_args) hinv44 h64 as ⟨v219, s45, hinv45, h_v219⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 h_v218 dropping he_v219 e_v219
          step as ⟨e_v220, he_v220⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s45 e_v220 (by rw [he_v220]; rfl) h_v219 h_v4 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v220, s46, hinv46, h_v220⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 h_v218 dropping h_v219 he_v220 e_v220 v219
          step as ⟨e_v221, he_v221⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s46 e_v221 (by rw [he_v221]; rfl) h_v218 h_v220 hinv46 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v221, s47, hinv47, h_v221⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 dropping h_v218 h_v220 he_v221 e_v221 v218 v220
          ite_done hinv47 hG with (eo_ite_true_rep _ hx_218 h_v221)
        · ite_branch hbv_218
          step as ⟨e_v222, he_v222⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v222 (by rw [he_v222]; exact empty_args) hinv43 h64 as ⟨v222, s44, hinv44, h_v222⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 dropping he_v222 e_v222
          step as ⟨e_v223, he_v223⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s44 e_v223 (by rw [he_v223]; rfl) h_v222 h_v4 hinv44 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v223, s45, hinv45, h_v223⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 dropping h_v222 he_v223 e_v223 v222
          ite_done hinv45 hG with (eo_ite_false_rep _ hx_218 h_v223)
        · ite_branch hbv_218
          ite_stuck hinv43 hG with hx_218)
      store_step with h_ite_v224 as ⟨v224, s44, hinv44, h_v224⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 dropping h_ite_v224 hinv43 s43
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v225, s45, hinv45, h_v225⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 h_v217 h_v224 dropping hinv44 s44
      step as ⟨e_v226, he_v226⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s45 e_v226 (by rw [he_v226]; rfl) h_v217 h_v224 h_v225 hinv45 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v226, s46, hinv46, h_v226⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 h_v216 dropping h_v217 h_v224 h_v225 he_v226 hinv45 e_v226 s45 v217 v224 v225
      store_step with ih.eo__24str_5funify_5fsplit s46 v216 v226 a0 _ _ _ hinv46 h64 (hG.rem hrem) h_v216 h_v226 h_a0 as ⟨v227, s47, hinv47, h_v227⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 h_v206 dropping h_v216 h_v226 hinv46 s46 v216 v226
      store_step with Store.apply_mk_rep s47 v206 v227 _ _ hinv47 h64 h_v206 h_v227 as ⟨v228, s48, hinv48, h_v228⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 dropping h_v206 h_v227 hinv47 s47 v206 v227
      store_step with ih.eo__24eo_5ftypeof s48 v228 _ hinv48 h64 (hG.rem hrem) h_v228 as ⟨v229, s49, hinv49, h_v229⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 dropping h_v228 hinv48 s48 v228
      store_step with ih.eo__24seq_5fempty s49 v229 _ hinv49 h64 (hG.rem hrem) h_v229 as ⟨v230, s50, hinv50, h_v230⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 h_v205 dropping h_v229 hinv49 s49 v229
      store_step with Store.apply_mk_rep s50 v205 v230 _ _ hinv50 h64 h_v205 h_v230 as ⟨v231, s51, hinv51, h_v231⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 h_v180 dropping h_v205 h_v230 hinv50 s50 v205 v230
      store_step with Store.apply_mk_rep s51 v180 v231 _ _ hinv51 h64 h_v180 h_v231 as ⟨v232, s52, hinv52, h_v232⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v179 dropping h_v180 h_v231 hinv51 s51 v180 v231
      store_step with Store.apply_mk_rep s52 v179 v232 _ _ hinv52 h64 h_v179 h_v232 as ⟨v233, s53, hinv53, h_v233⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 dropping h_v179 h_v232 hinv52 s52 v179 v232
      step as ⟨e_v234, he_v234⟩
      store_step with CtorSpec.eo_and.construct s53 e_v234 (by rw [he_v234]; exact empty_args) hinv53 h64 as ⟨v234, s54, hinv54, h_v234⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 dropping he_v234 hinv53 e_v234 s53
      step as ⟨e_v235, he_v235⟩
      store_step with CtorSpec.eo__3e.construct s54 e_v235 (by rw [he_v235]; exact empty_args) hinv54 h64 as ⟨v235, s55, hinv55, h_v235⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 dropping he_v235 hinv54 e_v235 s54
      step as ⟨e_v236, he_v236⟩
      store_step with CtorSpec.eo_str_2elen.construct s55 e_v236 (by rw [he_v236]; exact empty_args) hinv55 h64 as ⟨v236, s56, hinv56, h_v236⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 dropping he_v236 hinv55 e_v236 s55
      step as ⟨e_v237, he_v237⟩
      store_step with CtorSpec.eo__40purify.construct s56 e_v237 (by rw [he_v237]; exact empty_args) hinv56 h64 as ⟨v237, s57, hinv57, h_v237⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 dropping he_v237 hinv56 e_v237 s56
      step as ⟨e_v238, he_v238⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s57 e_v238 (by rw [he_v238]; exact empty_args) hinv57 h64 as ⟨v238, s58, hinv58, h_v238⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 dropping he_v238 hinv57 e_v238 s57
      have h_ite_v245 := (show if_21_eo__24eo_5fprog_5fconcat_5flprop s58 a0 v7 ⦃ r s' => s'.Inv ∧ s58.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_21_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s58
        rcases Store.boolean_value_term h_a0 with ⟨hx_239, hbv_239⟩ | ⟨hx_239, hbv_239⟩ | ⟨hx_239, hbv_239⟩
        · ite_branch hbv_239
          step as ⟨e_v239, he_v239⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s58 e_v239 (by rw [he_v239]; exact empty_args) hinv58 h64 as ⟨v239, s59, hinv59, h_v239⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 dropping he_v239 e_v239
          step as ⟨e_v240, he_v240⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s59 e_v240 (by rw [he_v240]; exact empty_args) hinv59 h64 as ⟨v240, s60, hinv60, h_v240⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 h_v239 dropping he_v240 e_v240
          step as ⟨e_v241, he_v241⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s60 e_v241 (by rw [he_v241]; rfl) h_v240 h_v7 hinv60 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v241, s61, hinv61, h_v241⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 h_v239 dropping h_v240 he_v241 e_v241 v240
          step as ⟨e_v242, he_v242⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s61 e_v242 (by rw [he_v242]; rfl) h_v239 h_v241 hinv61 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v242, s62, hinv62, h_v242⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 dropping h_v239 h_v241 he_v242 e_v242 v239 v241
          ite_done hinv62 hG with (eo_ite_true_rep _ hx_239 h_v242)
        · ite_branch hbv_239
          step as ⟨e_v243, he_v243⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s58 e_v243 (by rw [he_v243]; exact empty_args) hinv58 h64 as ⟨v243, s59, hinv59, h_v243⟩ growing hG carrying h_a0 h_v4 h_v7 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 dropping he_v243 e_v243
          step as ⟨e_v244, he_v244⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s59 e_v244 (by rw [he_v244]; rfl) h_v243 h_v7 hinv59 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v244, s60, hinv60, h_v244⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 dropping h_v243 h_v7 he_v244 e_v244 v243 v7
          ite_done hinv60 hG with (eo_ite_false_rep _ hx_239 h_v244)
        · ite_branch hbv_239
          ite_stuck hinv58 hG with hx_239)
      store_step with h_ite_v245 as ⟨v245, s59, hinv59, h_v245⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 dropping h_ite_v245 h_v7 hinv58 s58 v7
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s59 0#u32 (0) (by scalar_tac) hinv59 h64 as ⟨v246, s60, hinv60, h_v246⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v238 h_v245 dropping hinv59 s59
      step as ⟨e_v247, he_v247⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s60 e_v247 (by rw [he_v247]; rfl) h_v238 h_v245 h_v246 hinv60 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v247, s61, hinv61, h_v247⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 dropping h_v238 h_v245 h_v246 he_v247 hinv60 e_v247 s60 v238 v245 v246
      step as ⟨e_v248, he_v248⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s61 e_v248 (by rw [he_v248]; exact empty_args) hinv61 h64 as ⟨v248, s62, hinv62, h_v248⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 dropping he_v248 hinv61 e_v248 s61
      have h_ite_v255 := (show if_22_eo__24eo_5fprog_5fconcat_5flprop s62 a0 v4 ⦃ r s' => s'.Inv ∧ s62.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_22_eo__24eo_5fprog_5fconcat_5flprop
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s62
        rcases Store.boolean_value_term h_a0 with ⟨hx_249, hbv_249⟩ | ⟨hx_249, hbv_249⟩ | ⟨hx_249, hbv_249⟩
        · ite_branch hbv_249
          step as ⟨e_v249, he_v249⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s62 e_v249 (by rw [he_v249]; exact empty_args) hinv62 h64 as ⟨v249, s63, hinv63, h_v249⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 dropping he_v249 e_v249
          step as ⟨e_v250, he_v250⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s63 e_v250 (by rw [he_v250]; exact empty_args) hinv63 h64 as ⟨v250, s64, hinv64, h_v250⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 h_v249 dropping he_v250 e_v250
          step as ⟨e_v251, he_v251⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s64 e_v251 (by rw [he_v251]; rfl) h_v250 h_v4 hinv64 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v251, s65, hinv65, h_v251⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 h_v249 dropping h_v250 he_v251 e_v251 v250
          step as ⟨e_v252, he_v252⟩
          store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s65 e_v252 (by rw [he_v252]; rfl) h_v249 h_v251 hinv65 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v252, s66, hinv66, h_v252⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 dropping h_v249 h_v251 he_v252 e_v252 v249 v251
          ite_done hinv66 hG with (eo_ite_true_rep _ hx_249 h_v252)
        · ite_branch hbv_249
          step as ⟨e_v253, he_v253⟩
          store_step with CtorSpec.eo_str_2e_2b_2b.construct s62 e_v253 (by rw [he_v253]; exact empty_args) hinv62 h64 as ⟨v253, s63, hinv63, h_v253⟩ growing hG carrying h_a0 h_v4 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 dropping he_v253 e_v253
          step as ⟨e_v254, he_v254⟩
          store_step with Store.builtin_spec_list_singleton_intro n ih.eo__24eo_5fis_5flist_5fnil ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s63 e_v254 (by rw [he_v254]; rfl) h_v253 h_v4 hinv63 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_self_eo_str_2e_2b_2b as ⟨v254, s64, hinv64, h_v254⟩ growing hG carrying h_a0 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 dropping h_v253 h_v4 he_v254 e_v254 v253 v4
          ite_done hinv64 hG with (eo_ite_false_rep _ hx_249 h_v254)
        · ite_branch hbv_249
          ite_stuck hinv62 hG with hx_249)
      store_step with h_ite_v255 as ⟨v255, s63, hinv63, h_v255⟩ growing hG carrying h_a0 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 dropping h_ite_v255 h_v4 hinv62 s62 v4
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s63 0#u32 (0) (by scalar_tac) hinv63 h64 as ⟨v256, s64, hinv64, h_v256⟩ growing hG carrying h_a0 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 h_v248 h_v255 dropping hinv63 s63
      step as ⟨e_v257, he_v257⟩
      store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s64 e_v257 (by rw [he_v257]; rfl) h_v248 h_v255 h_v256 hinv64 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b as ⟨v257, s65, hinv65, h_v257⟩ growing hG carrying h_a0 h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 h_v247 dropping h_v248 h_v255 h_v256 he_v257 hinv64 e_v257 s64 v248 v255 v256
      store_step with ih.eo__24str_5funify_5fsplit s65 v247 v257 a0 _ _ _ hinv65 h64 (hG.rem hrem) h_v247 h_v257 h_a0 as ⟨v258, s66, hinv66, h_v258⟩ growing hG carrying h_v178 h_v233 h_v234 h_v235 h_v236 h_v237 dropping h_a0 h_v247 h_v257 hinv65 s65 v247 v257
      store_step with Store.apply_mk_rep s66 v237 v258 _ _ hinv66 h64 h_v237 h_v258 as ⟨v259, s67, hinv67, h_v259⟩ growing hG carrying h_v178 h_v233 h_v234 h_v235 h_v236 dropping h_v237 h_v258 hinv66 s66 v237 v258
      store_step with Store.apply_mk_rep s67 v236 v259 _ _ hinv67 h64 h_v236 h_v259 as ⟨v260, s68, hinv68, h_v260⟩ growing hG carrying h_v178 h_v233 h_v234 h_v235 dropping h_v236 h_v259 hinv67 s67 v236 v259
      store_step with Store.apply_mk_rep s68 v235 v260 _ _ hinv68 h64 h_v235 h_v260 as ⟨v261, s69, hinv69, h_v261⟩ growing hG carrying h_v178 h_v233 h_v234 dropping h_v235 h_v260 hinv68 s68 v235 v260
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s69 0#u32 (0) (by scalar_tac) hinv69 h64 as ⟨v262, s70, hinv70, h_v262⟩ growing hG carrying h_v178 h_v233 h_v234 h_v261 dropping hinv69 s69
      store_step with Store.apply_mk_rep s70 v261 v262 _ _ hinv70 h64 h_v261 h_v262 as ⟨v263, s71, hinv71, h_v263⟩ growing hG carrying h_v178 h_v233 h_v234 dropping h_v261 h_v262 hinv70 s70 v261 v262
      store_step with Store.apply_mk_rep s71 v234 v263 _ _ hinv71 h64 h_v234 h_v263 as ⟨v264, s72, hinv72, h_v264⟩ growing hG carrying h_v178 h_v233 dropping h_v234 h_v263 hinv71 s71 v234 v263
      store_step with Store.literal_boolean_spec s72 true hinv72 h64 as ⟨v265, s73, hinv73, h_v265⟩ growing hG carrying h_v178 h_v233 h_v264 dropping hinv72 s72
      store_step with Store.apply_mk_rep s73 v264 v265 _ _ hinv73 h64 h_v264 h_v265 as ⟨v266, s74, hinv74, h_v266⟩ growing hG carrying h_v178 h_v233 dropping h_v264 h_v265 hinv73 s73 v264 v265
      store_step with Store.apply_mk_rep s74 v233 v266 _ _ hinv74 h64 h_v233 h_v266 as ⟨v267, s75, hinv75, h_v267⟩ growing hG carrying h_v178 dropping h_v233 h_v266 hinv74 s74 v233 v266
      store_step with Store.apply_mk_rep s75 v178 v267 _ _ hinv75 h64 h_v178 h_v267 as ⟨v268, s76, hinv76, h_v268⟩ growing hG carrying dropping h_v178 h_v267 hinv75 s75 v178 v267
      req_done hinv76 hG with h_v268 using hq_v45)
    store_step with h_req_v269 as ⟨v269, s77, hinv77, h_v269⟩ growing hG carrying dropping h_req_v269 h_v24 h_v4 h_v45 h_v7 hinv12 s12 v24 v4 v45 v7
    req_done hinv77 hG with h_v269 using hq_v35)
  store_step with h_req_v270 as ⟨v270, s78, hinv78, h_v270⟩ growing hG carrying dropping h_req_v270 h_v20 h_v24 h_v35 h_v4 h_v7 hinv8 s8 v20 v24 v35 v4 v7
  case_done hinv78 hG with h_v270 in EoCases.__eo_prog_concat_lprop.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v12 hn_v13 hn_v15 hn_v16 hn_v19 hn_v20 hn_v23 hn_v24

/-- logos's `__eo_prog_concat_lprop` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fconcat_5flprop.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_concat_lprop x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_concat_lprop.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_concat_lprop
  unfold EoCases.__eo_prog_concat_lprop.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fconcat_5flprop_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fconcat_5flprop s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_concat_lprop x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fconcat_5flprop.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fconcat_5flprop
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fconcat_5flprop_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_concat_lprop.case_0

theorem eo__24eo_5fprog_5fconcat_5flprop_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fconcat_5flprop.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fconcat_5flprop
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fconcat_5flprop s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_concat_lprop x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fconcat_5flprop_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
