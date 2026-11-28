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

theorem case_0_eo__24eo_5fprog_5fsets_2dunion_2dmember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fsets_2dunion_2dmember s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_sets_union_member.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_sets_union_member.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsets_2dunion_2dmember
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_set_2emember.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2eunion.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_or.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v7 dropping he_v8 hinv8 e_v8 s8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_set_2emember.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v7 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v7 h_v8 dropping h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v10 a1 _ _ hinv11 h64 h_v10 h_a1 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a2 h_v7 h_v8 dropping h_a1 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v8 v11 _ _ hinv12 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a2 h_v7 dropping h_v11 h_v8 hinv12 s12 v11 v8
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a2 h_v7 h_v12 dropping he_v13 hinv13 e_v13 s13
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_set_2emember.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a2 h_v7 h_v12 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a0 _ _ hinv15 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_v7 h_v12 h_v13 dropping h_a0 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v15 a2 _ _ hinv16 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_v7 h_v12 h_v13 dropping h_a2 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v13 v16 _ _ hinv17 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v7 h_v12 dropping h_v13 h_v16 hinv17 s17 v13 v16
  store_step with Store.literal_boolean_spec s18 false hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_v7 h_v12 h_v17 dropping hinv18 s18
  store_step with Store.apply_rep s19 v17 v18 _ _ hinv19 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_v7 h_v12 dropping h_v17 h_v18 hinv19 s19 v17 v18
  store_step with Store.apply_rep s20 v12 v19 _ _ hinv20 h64 h_v12 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_v7 dropping h_v12 h_v19 hinv20 s20 v12 v19
  store_step with Store.apply_rep s21 v7 v20 _ _ hinv21 h64 h_v7 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying dropping h_v20 h_v7 hinv21 s21 v20 v7
  case_done hinv22 hG with h_v21 in EoCases.__eo_prog_sets_union_member.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_sets_union_member` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsets_2dunion_2dmember.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_sets_union_member x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_sets_union_member.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_sets_union_member
  unfold EoCases.__eo_prog_sets_union_member.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsets_2dunion_2dmember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fsets_2dunion_2dmember s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_member x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsets_2dunion_2dmember.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fsets_2dunion_2dmember
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fsets_2dunion_2dmember_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_sets_union_member.case_0

theorem eo__24eo_5fprog_5fsets_2dunion_2dmember_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsets_2dunion_2dmember.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fsets_2dunion_2dmember
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsets_2dunion_2dmember s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_sets_union_member x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsets_2dunion_2dmember_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsets_2dunion_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fsets_2dunion_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_sets_union_self.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_sets_union_self.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsets_2dunion_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_set_2eunion.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying dropping h_a0 h_v4 hinv5 s5 v4
  case_done hinv6 hG with h_v5 in EoCases.__eo_prog_sets_union_self.case_0 using hn_a0

/-- logos's `__eo_prog_sets_union_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsets_2dunion_2dself.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_sets_union_self x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_sets_union_self.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_sets_union_self
  unfold EoCases.__eo_prog_sets_union_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsets_2dunion_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsets_2dunion_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_union_self x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsets_2dunion_2dself.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsets_2dunion_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fsets_2dunion_2dself_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_sets_union_self.case_0

theorem eo__24eo_5fprog_5fsets_2dunion_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsets_2dunion_2dself.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsets_2dunion_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsets_2dunion_2dself s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_sets_union_self x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsets_2dunion_2dself_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_sets_choose_member.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_sets_choose_member.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_sets_choose_member.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_set_2echoose.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_sets_choose_member.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_or.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with Store.apply_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 hinv3 s3 v5
  store_step with ih.eo__24eo_5ftypeof s4 v2 _ hinv4 h64 (hG.rem hrem) h_v2 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v6 dropping hinv4 s4
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_set_2eempty.construct s5 e_v8 (by rw [he_v8]; rfl) h_v7 hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 h_v6 dropping h_v7 he_v8 hinv5 e_v8 s5 v7
  store_step with Store.apply_mk_rep s6 v6 v8 _ _ hinv6 h64 h_v6 h_v8 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 dropping h_v6 h_v8 hinv6 s6 v6 v8
  store_step with Store.apply_mk_rep s7 v4 v9 _ _ hinv7 h64 h_v4 h_v9 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 dropping h_v4 h_v9 hinv7 s7 v4 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v10 dropping he_v11 hinv8 e_v11 s8
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_set_2emember.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v10 h_v11 dropping he_v12 hinv9 e_v12 s9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_set_2echoose.construct s10 e_v13 (by rw [he_v13]; exact empty_args) hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v10 h_v11 h_v12 dropping he_v13 hinv10 e_v13 s10
  store_step with Store.apply_rep s11 v13 v2 _ _ hinv11 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v10 h_v11 h_v12 dropping h_v13 hinv11 s11 v13
  store_step with Store.apply_rep s12 v12 v14 _ _ hinv12 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v10 h_v11 dropping h_v12 h_v14 hinv12 s12 v12 v14
  store_step with Store.apply_rep s13 v15 v2 _ _ hinv13 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v10 h_v11 dropping h_v15 h_v2 hinv13 s13 v15 v2
  store_step with Store.apply_rep s14 v11 v16 _ _ hinv14 h64 h_v11 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v10 dropping h_v11 h_v16 hinv14 s14 v11 v16
  store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v10 h_v17 dropping hinv15 s15
  store_step with Store.apply_rep s16 v17 v18 _ _ hinv16 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v10 dropping h_v17 h_v18 hinv16 s16 v17 v18
  store_step with Store.apply_mk_rep s17 v10 v19 _ _ hinv17 h64 h_v10 h_v19 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying dropping h_v10 h_v19 hinv17 s17 v10 v19
  case_done hinv18 hG with h_v20 in EoCases.__eo_prog_sets_choose_member.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_prog_sets_choose_member` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsets_5fchoose_5fmember.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_sets_choose_member x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_sets_choose_member.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_sets_choose_member
  unfold EoCases.__eo_prog_sets_choose_member.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsets_5fchoose_5fmember_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsets_5fchoose_5fmember s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_choose_member x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsets_5fchoose_5fmember.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsets_5fchoose_5fmember
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_sets_choose_member.case_0

theorem eo__24eo_5fprog_5fsets_5fchoose_5fmember_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsets_5fchoose_5fmember.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsets_5fchoose_5fmember
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsets_5fchoose_5fmember s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_sets_choose_member x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsets_5fchoose_5fmember_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsets_5fext_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fsets_5fext s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_sets_ext.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_sets_ext.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsets_5fext
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_sets_ext.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_sets_ext.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_sets_ext.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_sets_ext.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_sets_ext.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_sets_ext.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v8 h_v11 h_v13 dropping he_v14 hinv3 e_v14 s3
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_set_2emember.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v8 h_v11 h_v13 h_v14 dropping he_v15 hinv4 e_v15 s4
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__40sets_5fdeq_5fdiff.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v8 h_v11 h_v13 h_v14 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with Store.apply_rep s6 v16 v11 _ _ hinv6 h64 h_v16 h_v11 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v8 h_v11 h_v13 h_v14 h_v15 dropping h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v17 v8 _ _ hinv7 h64 h_v17 h_v8 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v8 h_v11 h_v13 h_v14 h_v15 dropping h_v17 hinv7 s7 v17
  store_step with Store.apply_rep s8 v15 v18 _ _ hinv8 h64 h_v15 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v8 h_v11 h_v13 h_v14 dropping h_v15 h_v18 hinv8 s8 v15 v18
  store_step with Store.apply_rep s9 v19 v11 _ _ hinv9 h64 h_v19 h_v11 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v8 h_v11 h_v13 h_v14 dropping h_v19 hinv9 s9 v19
  store_step with Store.apply_rep s10 v14 v20 _ _ hinv10 h64 h_v14 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_v8 h_v11 h_v13 dropping h_v14 h_v20 hinv10 s10 v14 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_set_2emember.construct s11 e_v22 (by rw [he_v22]; exact empty_args) hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v8 h_v11 h_v13 h_v21 dropping he_v22 hinv11 e_v22 s11
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__40sets_5fdeq_5fdiff.construct s12 e_v23 (by rw [he_v23]; exact empty_args) hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_v8 h_v11 h_v13 h_v21 h_v22 dropping he_v23 hinv12 e_v23 s12
  store_step with Store.apply_rep s13 v23 v11 _ _ hinv13 h64 h_v23 h_v11 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_v8 h_v13 h_v21 h_v22 dropping h_v11 h_v23 hinv13 s13 v11 v23
  store_step with Store.apply_rep s14 v24 v8 _ _ hinv14 h64 h_v24 h_v8 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_v8 h_v13 h_v21 h_v22 dropping h_v24 hinv14 s14 v24
  store_step with Store.apply_rep s15 v22 v25 _ _ hinv15 h64 h_v22 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_v8 h_v13 h_v21 dropping h_v22 h_v25 hinv15 s15 v22 v25
  store_step with Store.apply_rep s16 v26 v8 _ _ hinv16 h64 h_v26 h_v8 (by ns_tac) (by ns_tac) as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_v13 h_v21 dropping h_v26 h_v8 hinv16 s16 v26 v8
  store_step with Store.apply_rep s17 v21 v27 _ _ hinv17 h64 h_v21 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_v13 dropping h_v21 h_v27 hinv17 s17 v21 v27
  store_step with Store.apply_rep s18 v13 v28 _ _ hinv18 h64 h_v13 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying dropping h_v13 h_v28 hinv18 s18 v13 v28
  case_done hinv19 hG with h_v29 in EoCases.__eo_prog_sets_ext.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_sets_ext` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsets_5fext.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_sets_ext x_a0 =
      (firstSome [EoCases.__eo_prog_sets_ext.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_sets_ext
  unfold EoCases.__eo_prog_sets_ext.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsets_5fext_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsets_5fext s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_ext x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsets_5fext.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsets_5fext
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fsets_5fext_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_sets_ext.case_0

theorem eo__24eo_5fprog_5fsets_5fext_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsets_5fext.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsets_5fext
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsets_5fext s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_sets_ext x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsets_5fext_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_sets_singleton_inj.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_sets_singleton_inj.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a0 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_set_2esingleton.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  pat_unapply h_v4 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_set_2esingleton.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_v11 h_v14 h_v15 dropping h_v10 h_v12 h_v4 he_v16 hinv2 e_v16 s2 v10 v12 v4
  pat_same v14 v16 with h_v14 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_sets_singleton_inj.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_v11 h_v15 dropping h_v14 h_v16 he_v17 hinv3 e_v17 s3 v14 v16
  store_step with Store.apply_rep s4 v17 v11 _ _ hinv4 h64 h_v17 h_v11 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_v15 dropping h_v11 h_v17 hinv4 s4 v11 v17
  store_step with Store.apply_rep s5 v18 v15 _ _ hinv5 h64 h_v18 h_v15 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying dropping h_v15 h_v18 hinv5 s5 v15 v18
  case_done hinv6 hG with h_v19 in EoCases.__eo_prog_sets_singleton_inj.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15

/-- logos's `__eo_prog_sets_singleton_inj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsets_5fsingleton_5finj.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_sets_singleton_inj x_a0 =
      (firstSome [EoCases.__eo_prog_sets_singleton_inj.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_sets_singleton_inj
  unfold EoCases.__eo_prog_sets_singleton_inj.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsets_5fsingleton_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsets_5fsingleton_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_sets_singleton_inj x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsets_5fsingleton_5finj.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsets_5fsingleton_5finj
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_sets_singleton_inj.case_0

theorem eo__24eo_5fprog_5fsets_5fsingleton_5finj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsets_5fsingleton_5finj.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsets_5fsingleton_5finj
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsets_5fsingleton_5finj s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_sets_singleton_inj x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsets_5fsingleton_5finj_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fskolem_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fskolem_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_skolem_intro.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_skolem_intro.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fskolem_5fintro
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_skolem_intro.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40purify.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_skolem_intro.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__40purify.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with Store.apply_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 hinv3 s3 v5
  store_step with Store.apply_rep s4 v4 v6 _ _ hinv4 h64 h_v4 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v6 hinv4 s4 v4 v6
  store_step with Store.apply_rep s5 v7 v2 _ _ hinv5 h64 h_v7 h_v2 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying dropping h_v2 h_v7 hinv5 s5 v2 v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_prog_skolem_intro.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_prog_skolem_intro` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fskolem_5fintro.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_skolem_intro x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_skolem_intro.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_skolem_intro
  unfold EoCases.__eo_prog_skolem_intro.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fskolem_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fskolem_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_skolem_intro x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fskolem_5fintro.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fskolem_5fintro
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fskolem_5fintro_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_skolem_intro.case_0

theorem eo__24eo_5fprog_5fskolem_5fintro_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fskolem_5fintro.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fskolem_5fintro
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fskolem_5fintro s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_skolem_intro x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fskolem_5fintro_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fskolemize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_skolemize.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_skolemize.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fskolemize
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_skolemize.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_skolemize.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_skolemize.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_skolemize.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_skolemize.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_skolemize.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  store_step with Store.apply_rep s3 v13 v11 _ _ hinv3 h64 h_v13 h_v11 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v8 h_v11 dropping h_v13 hinv3 s3 v13
  store_step with Store.apply_rep s4 v14 v8 _ _ hinv4 h64 h_v14 h_v8 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v8 h_v11 dropping h_v14 hinv4 s4 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v8 h_v11 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with ih.eo__24is_5fclosed_5frec s6 v15 v16 _ _ hinv6 h64 (hG.rem hrem) h_v15 h_v16 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v8 h_v11 dropping h_v15 h_v16 hinv6 s6 v15 v16
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v8 h_v11 h_v17 dropping hinv7 s7
  have h_req_v32 := (show requires_1_eo__24eo_5fprog_5fskolemize s8 v17 v18 v11 v8 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fskolemize
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v17 v18 with h_v17 h_v18 using hinv8 hG
    req_stuck h_v17 as hq_v17 using hinv8 hG
    step as ⟨e_v19, he_v19⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s8 e_v19 (by rw [he_v19]; exact empty_args) hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v8 h_v11 dropping h_v17 h_v18 he_v19 hinv8 e_v19 s8 v17 v18
    step as ⟨e_v20, he_v20⟩
    store_step with Store.builtin_spec_list_setof n ih.eo__24eo_5fis_5flist_5fnil s9 e_v20 (by rw [he_v20]; rfl) h_v19 h_v11 hinv9 h64 (hG.rem hrem) (by not_left_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v8 h_v11 dropping h_v19 he_v20 hinv9 e_v20 s9 v19
    have h_req_v31 := (show requires_0_eo__24eo_5fprog_5fskolemize s10 v20 v11 v8 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fskolemize
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s10
      req_same v20 v11 with h_v20 h_v11 using hinv10 hG
      req_stuck h_v20 as hq_v20 using hinv10 hG
      store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_v8 h_v11 dropping h_v20 hinv10 s10 v20
      step as ⟨e_v22, he_v22⟩
      store_step with CtorSpec.eo_not.construct s11 e_v22 (by rw [he_v22]; exact empty_args) hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v8 h_v11 h_v21 dropping he_v22 hinv11 e_v22 s11
      store_step with Store.apply_rep s12 v22 v8 _ _ hinv12 h64 h_v22 h_v8 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_v8 h_v11 h_v21 dropping h_v22 hinv12 s12 v22
      step as ⟨e_v24, he_v24⟩
      store_step with CtorSpec.eo_forall.construct s13 e_v24 (by rw [he_v24]; exact empty_args) hinv13 h64 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_v8 h_v11 h_v21 h_v23 dropping he_v24 hinv13 e_v24 s13
      store_step with Store.apply_rep s14 v24 v11 _ _ hinv14 h64 h_v24 h_v11 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_v8 h_v11 h_v21 h_v23 dropping h_v24 hinv14 s14 v24
      store_step with Store.apply_rep s15 v25 v8 _ _ hinv15 h64 h_v25 h_v8 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_v11 h_v21 h_v23 dropping h_v25 h_v8 hinv15 s15 v25 v8
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_v11 h_v21 h_v23 h_v26 dropping hinv16 s16
      store_step with ih.eo__24mk_5fskolems s17 v11 v26 v27 _ _ _ hinv17 h64 (hG.rem hrem) h_v11 h_v26 h_v27 as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_v11 h_v21 h_v23 dropping h_v26 h_v27 hinv17 s17 v26 v27
      step as ⟨e_v29, he_v29⟩
      store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s18 e_v29 (by rw [he_v29]; exact empty_args) hinv18 h64 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_v11 h_v21 h_v23 h_v28 dropping he_v29 hinv18 e_v29 s18
      store_step with ih.eo__24substitute_5fsimul_5frec s19 v21 v23 v11 v28 v29 _ _ _ _ _ hinv19 h64 (hG.rem hrem) h_v21 h_v23 h_v11 h_v28 h_v29 as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying dropping h_v11 h_v21 h_v23 h_v28 h_v29 hinv19 s19 v11 v21 v23 v28 v29
      req_done hinv20 hG with h_v30 using hq_v20)
    store_step with h_req_v31 as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying dropping h_req_v31 h_v11 h_v20 h_v8 hinv10 s10 v11 v20 v8
    req_done hinv21 hG with h_v31 using hq_v17)
  store_step with h_req_v32 as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying dropping h_req_v32 h_v11 h_v17 h_v18 h_v8 hinv8 s8 v11 v17 v18 v8
  case_done hinv22 hG with h_v32 in EoCases.__eo_prog_skolemize.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_skolemize` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fskolemize.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_skolemize x_a0 =
      (firstSome [EoCases.__eo_prog_skolemize.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_skolemize
  unfold EoCases.__eo_prog_skolemize.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fskolemize_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fskolemize s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_skolemize x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fskolemize.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fskolemize
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fskolemize_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_skolemize.case_0

theorem eo__24eo_5fprog_5fskolemize_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fskolemize.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fskolemize
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fskolemize s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_skolemize x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fskolemize_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_split.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_split.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsplit
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 dropping h_v0 hinv1 s1 v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_or.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v1 dropping he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v1 h_v2 dropping h_a0 h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v1 dropping h_v2 h_v4 hinv5 s5 v2 v4
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v1 h_v5 dropping hinv6 s6
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v1 dropping h_v5 h_v6 hinv7 s7 v5 v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v1 h_v7 hinv8 s8 v1 v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_split.case_0 using hn_a0

/-- logos's `__eo_prog_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsplit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_split x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_split.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_split
  unfold EoCases.__eo_prog_split.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_split x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsplit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fsplit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_split.case_0

theorem eo__24eo_5fprog_5fsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsplit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsplit s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_split x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsplit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dat_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dat_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_at_elim.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_at_elim.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dat_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eat.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 h_v4 dropping h_a0 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a1 h_v6 hinv7 s7 v6
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 1#u32 (1) (by scalar_tac) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v4 h_v7 dropping hinv8 s8
  store_step with Store.apply_rep s9 v7 v8 _ _ hinv9 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v4 dropping h_v7 h_v8 hinv9 s9 v7 v8
  store_step with Store.apply_rep s10 v4 v9 _ _ hinv10 h64 h_v4 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_v4 h_v9 hinv10 s10 v4 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_str_at_elim.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_at_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dat_2delim.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_at_elim x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_at_elim.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_at_elim
  unfold EoCases.__eo_prog_str_at_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dat_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dat_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_at_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dat_2delim.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dat_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dat_2delim_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_at_elim.case_0

theorem eo__24eo_5fprog_5fstr_2dat_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dat_2delim.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dat_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dat_2delim s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_at_elim x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dat_2delim_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_concat_clash.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_concat_clash.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_concat_clash.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_clash.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_concat_clash.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_concat_clash.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 h_v23 h_v24 dropping h_a5 h_v16 h_v18 h_v20 h_v4 he_v25 hinv3 e_v25 s3 v16 v18 v20 v4
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_concat_clash.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 h_v27 h_v28 dropping h_v23 h_v24 h_v25 he_v29 hinv4 e_v29 s4 v23 v24 v25
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_same v28 a0 with h_v28 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_unapply h_v21 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_concat_clash.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2elen.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v21 h_v27 h_v28 h_v29 he_v33 hinv5 e_v33 s5 v21 v27 v28 v29
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_concat_clash.case_0
  pat_same v32 a2 with h_v32 h_a2 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_concat_clash.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v31 h_v32 h_v33 he_v34 hinv6 e_v34 s6 v31 v32 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping he_v35 hinv7 e_v35 s7
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s8 e_v36 (by rw [he_v36]; exact empty_args) hinv8 h64 as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 h_v35 dropping he_v36 hinv8 e_v36 s8
  store_step with Store.apply_rep s9 v36 a0 _ _ hinv9 h64 h_v36 h_a0 (by ns_tac) (by ns_tac) as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a1 h_a2 h_a3 h_v34 h_v35 dropping h_a0 h_v36 hinv9 s9 v36
  store_step with Store.apply_rep s10 v37 a1 _ _ hinv10 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a2 h_a3 h_v34 h_v35 dropping h_a1 h_v37 hinv10 s10 v37
  store_step with Store.apply_rep s11 v35 v38 _ _ hinv11 h64 h_v35 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a2 h_a3 h_v34 dropping h_v35 h_v38 hinv11 s11 v35 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s12 e_v40 (by rw [he_v40]; exact empty_args) hinv12 h64 as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a2 h_a3 h_v34 h_v39 dropping he_v40 hinv12 e_v40 s12
  store_step with Store.apply_rep s13 v40 a2 _ _ hinv13 h64 h_v40 h_a2 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a3 h_v34 h_v39 dropping h_a2 h_v40 hinv13 s13 v40
  store_step with Store.apply_rep s14 v41 a3 _ _ hinv14 h64 h_v41 h_a3 (by ns_tac) (by ns_tac) as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_v34 h_v39 dropping h_a3 h_v41 hinv14 s14 v41
  store_step with Store.apply_rep s15 v39 v42 _ _ hinv15 h64 h_v39 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_v34 dropping h_v39 h_v42 hinv15 s15 v39 v42
  store_step with Store.apply_rep s16 v34 v43 _ _ hinv16 h64 h_v34 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying dropping h_v34 h_v43 hinv16 s16 v34 v43
  store_step with Store.literal_boolean_spec s17 false hinv17 h64 as ⟨v45, s18, hinv18, h_v45⟩ growing hG carrying h_v44 dropping hinv17 s17
  store_step with Store.apply_rep s18 v44 v45 _ _ hinv18 h64 h_v44 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s19, hinv19, h_v46⟩ growing hG carrying dropping h_v44 h_v45 hinv18 s18 v44 v45
  case_done hinv19 hG with h_v46 in EoCases.__eo_prog_str_concat_clash.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v31 hn_v32

/-- logos's `__eo_prog_str_concat_clash` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dconcat_2dclash.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_concat_clash x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_concat_clash.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_concat_clash
  unfold EoCases.__eo_prog_str_concat_clash.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dconcat_2dclash_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dconcat_2dclash s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_clash x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dconcat_2dclash.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dconcat_2dclash
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_concat_clash.case_0

theorem eo__24eo_5fprog_5fstr_2dconcat_2dclash_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dconcat_2dclash.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dconcat_2dclash
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dconcat_2dclash s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_concat_clash x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dconcat_2dclash_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_concat_clash2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_concat_clash2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_concat_clash2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 h_v23 h_v24 dropping h_a4 h_v16 h_v18 h_v20 h_v4 he_v25 hinv3 e_v25 s3 v16 v18 v20 v4
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 h_v27 h_v28 dropping h_v23 h_v24 h_v25 he_v29 hinv4 e_v29 s4 v23 v24 v25
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_same v28 a0 with h_v28 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_unapply h_v21 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2elen.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v31 h_v32 dropping h_v21 h_v27 h_v28 h_v29 he_v33 hinv5 e_v33 s5 v21 v27 v28 v29
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  pat_same v32 a1 with h_v32 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_concat_clash2.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v31 h_v32 h_v33 he_v34 hinv6 e_v34 s6 v31 v32 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v34 dropping he_v35 hinv7 e_v35 s7
  store_step with Store.apply_rep s8 v35 a0 _ _ hinv8 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a1 h_a2 h_v34 dropping h_a0 h_v35 hinv8 s8 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a1 h_a2 h_v34 h_v36 dropping he_v37 hinv9 e_v37 s9
  store_step with Store.apply_rep s10 v37 a1 _ _ hinv10 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a2 h_v34 h_v36 dropping h_a1 h_v37 hinv10 s10 v37
  store_step with Store.apply_rep s11 v38 a2 _ _ hinv11 h64 h_v38 h_a2 (by ns_tac) (by ns_tac) as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_v34 h_v36 dropping h_a2 h_v38 hinv11 s11 v38
  store_step with Store.apply_rep s12 v36 v39 _ _ hinv12 h64 h_v36 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_v34 dropping h_v36 h_v39 hinv12 s12 v36 v39
  store_step with Store.apply_rep s13 v34 v40 _ _ hinv13 h64 h_v34 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying dropping h_v34 h_v40 hinv13 s13 v34 v40
  store_step with Store.literal_boolean_spec s14 false hinv14 h64 as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_v41 dropping hinv14 s14
  store_step with Store.apply_rep s15 v41 v42 _ _ hinv15 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying dropping h_v41 h_v42 hinv15 s15 v41 v42
  case_done hinv16 hG with h_v43 in EoCases.__eo_prog_str_concat_clash2.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v31 hn_v32

/-- logos's `__eo_prog_str_concat_clash2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dconcat_2dclash2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_concat_clash2 x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_concat_clash2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_concat_clash2
  unfold EoCases.__eo_prog_str_concat_clash2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2 s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_clash2 x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dconcat_2dclash2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_concat_clash2.case_0

theorem eo__24eo_5fprog_5fstr_2dconcat_2dclash2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dconcat_2dclash2.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2dconcat_2dclash2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2 s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_concat_clash2 x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_concat_unify.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_concat_unify.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 dropping h_v3 h_v6 hinv7 s7 v3 v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 dropping h_v1 h_v7 hinv8 s8 v1 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v0 h_v8 dropping h_a0 h_v9 hinv10 s10 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v0 h_v8 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v11 a3 _ _ hinv12 h64 h_v11 h_a3 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v0 h_v8 h_v10 dropping h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a4 _ _ hinv13 h64 h_v12 h_a4 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v0 h_v8 h_v10 dropping h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v10 v13 _ _ hinv14 h64 h_v10 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v0 h_v8 dropping h_v10 h_v13 hinv14 s14 v10 v13
  store_step with Store.apply_rep s15 v8 v14 _ _ hinv15 h64 h_v8 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v0 dropping h_v14 h_v8 hinv15 s15 v14 v8
  store_step with Store.apply_rep s16 v0 v15 _ _ hinv16 h64 h_v0 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 dropping h_v0 h_v15 hinv16 s16 v0 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v16 dropping he_v17 hinv17 e_v17 s17
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s18 e_v18 (by rw [he_v18]; exact empty_args) hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v16 h_v17 dropping he_v18 hinv18 e_v18 s18
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v19 (by rw [he_v19]; exact empty_args) hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v16 h_v17 h_v18 dropping he_v19 hinv19 e_v19 s19
  store_step with Store.apply_rep s20 v19 a1 _ _ hinv20 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a2 h_a3 h_a4 h_v16 h_v17 h_v18 dropping h_a1 h_v19 hinv20 s20 v19
  store_step with Store.apply_rep s21 v20 a2 _ _ hinv21 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a3 h_a4 h_v16 h_v17 h_v18 dropping h_a2 h_v20 hinv21 s21 v20
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s22 e_v22 (by rw [he_v22]; rfl) h_v18 h_v21 hinv22 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a3 h_a4 h_v16 h_v17 dropping h_v18 h_v21 he_v22 hinv22 e_v22 s22 v18 v21
  store_step with Store.apply_mk_rep s23 v17 v22 _ _ hinv23 h64 h_v17 h_v22 as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a3 h_a4 h_v16 dropping h_v17 h_v22 hinv23 s23 v17 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s24 e_v24 (by rw [he_v24]; exact empty_args) hinv24 h64 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a3 h_a4 h_v16 h_v23 dropping he_v24 hinv24 e_v24 s24
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s25 e_v25 (by rw [he_v25]; exact empty_args) hinv25 h64 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a3 h_a4 h_v16 h_v23 h_v24 dropping he_v25 hinv25 e_v25 s25
  store_step with Store.apply_rep s26 v25 a3 _ _ hinv26 h64 h_v25 h_a3 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a4 h_v16 h_v23 h_v24 dropping h_a3 h_v25 hinv26 s26 v25
  store_step with Store.apply_rep s27 v26 a4 _ _ hinv27 h64 h_v26 h_a4 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_v16 h_v23 h_v24 dropping h_a4 h_v26 hinv27 s27 v26
  step as ⟨e_v28, he_v28⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s28 e_v28 (by rw [he_v28]; rfl) h_v24 h_v27 hinv28 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying h_v16 h_v23 dropping h_v24 h_v27 he_v28 hinv28 e_v28 s28 v24 v27
  store_step with Store.apply_mk_rep s29 v23 v28 _ _ hinv29 h64 h_v23 h_v28 as ⟨v29, s30, hinv30, h_v29⟩ growing hG carrying h_v16 dropping h_v23 h_v28 hinv29 s29 v23 v28
  store_step with Store.apply_mk_rep s30 v16 v29 _ _ hinv30 h64 h_v16 h_v29 as ⟨v30, s31, hinv31, h_v30⟩ growing hG carrying dropping h_v16 h_v29 hinv30 s30 v16 v29
  case_done hinv31 hG with h_v30 in EoCases.__eo_prog_str_concat_unify.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

/-- logos's `__eo_prog_str_concat_unify` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dconcat_2dunify.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_concat_unify x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_concat_unify.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_concat_unify
  unfold EoCases.__eo_prog_str_concat_unify.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2dconcat_2dunify s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_unify x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dconcat_2dunify.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2dconcat_2dunify
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_concat_unify.case_0

theorem eo__24eo_5fprog_5fstr_2dconcat_2dunify_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dconcat_2dunify.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2dconcat_2dunify
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dconcat_2dunify s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_concat_unify x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_concat_unify_base.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_concat_unify_base.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase
  have hG := Store.Grows.refl s
  pat_unapply h_a3 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_str_concat_unify_base.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 dropping h_a3 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_concat_unify_base.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with Store.apply_rep s3 v5 a0 _ _ hinv3 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v4 dropping h_v5 hinv3 s3 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v4 h_v6 dropping he_v7 hinv4 e_v7 s4
  store_step with Store.apply_rep s5 v7 a0 _ _ hinv5 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v6 dropping h_a0 h_v7 hinv5 s5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v6 h_v8 dropping he_v9 hinv6 e_v9 s6
  store_step with Store.apply_rep s7 v9 a1 _ _ hinv7 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v6 h_v8 dropping h_v9 hinv7 s7 v9
  store_step with Store.apply_rep s8 v10 a2 _ _ hinv8 h64 h_v10 h_a2 (by ns_tac) (by ns_tac) as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v6 h_v8 dropping h_v10 hinv8 s8 v10
  store_step with Store.apply_rep s9 v8 v11 _ _ hinv9 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v6 dropping h_v11 h_v8 hinv9 s9 v11 v8
  store_step with Store.apply_rep s10 v6 v12 _ _ hinv10 h64 h_v6 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 dropping h_v12 h_v6 hinv10 s10 v12 v6
  store_step with Store.apply_rep s11 v4 v13 _ _ hinv11 h64 h_v4 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_a1 h_a2 h_v2 dropping h_v13 h_v4 hinv11 s11 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v15 (by rw [he_v15]; exact empty_args) hinv12 h64 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_a1 h_a2 h_v2 h_v14 dropping he_v15 hinv12 e_v15 s12
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_Seq.construct s13 e_v16 (by rw [he_v16]; exact empty_args) hinv13 h64 as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_a1 h_a2 h_v2 h_v14 h_v15 dropping he_v16 hinv13 e_v16 s13
  store_step with Store.apply_rep s14 v16 v2 _ _ hinv14 h64 h_v16 h_v2 (by ns_tac) (by ns_tac) as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_a1 h_a2 h_v14 h_v15 dropping h_v16 h_v2 hinv14 s14 v16 v2
  store_step with ih.eo__24seq_5fempty s15 v17 _ hinv15 h64 (hG.rem hrem) h_v17 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_a1 h_a2 h_v14 h_v15 dropping h_v17 hinv15 s15 v17
  store_step with Store.apply_mk_rep s16 v15 v18 _ _ hinv16 h64 h_v15 h_v18 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_a1 h_a2 h_v14 dropping h_v15 h_v18 hinv16 s16 v15 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v20 (by rw [he_v20]; exact empty_args) hinv17 h64 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_a1 h_a2 h_v14 h_v19 dropping he_v20 hinv17 e_v20 s17
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s18 e_v21 (by rw [he_v21]; exact empty_args) hinv18 h64 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_a1 h_a2 h_v14 h_v19 h_v20 dropping he_v21 hinv18 e_v21 s18
  store_step with Store.apply_rep s19 v21 a1 _ _ hinv19 h64 h_v21 h_a1 (by ns_tac) (by ns_tac) as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_a2 h_v14 h_v19 h_v20 dropping h_a1 h_v21 hinv19 s19 v21
  store_step with Store.apply_rep s20 v22 a2 _ _ hinv20 h64 h_v22 h_a2 (by ns_tac) (by ns_tac) as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v14 h_v19 h_v20 dropping h_a2 h_v22 hinv20 s20 v22
  step as ⟨e_v24, he_v24⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s21 e_v24 (by rw [he_v24]; rfl) h_v20 h_v23 hinv21 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v14 h_v19 dropping h_v20 h_v23 he_v24 hinv21 e_v24 s21 v20 v23
  store_step with Store.apply_mk_rep s22 v19 v24 _ _ hinv22 h64 h_v19 h_v24 as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v14 dropping h_v19 h_v24 hinv22 s22 v19 v24
  store_step with Store.apply_mk_rep s23 v14 v25 _ _ hinv23 h64 h_v14 h_v25 as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying dropping h_v14 h_v25 hinv23 s23 v14 v25
  case_done hinv24 hG with h_v26 in EoCases.__eo_prog_str_concat_unify_base.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2

/-- logos's `__eo_prog_str_concat_unify_base` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_concat_unify_base x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_concat_unify_base.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_concat_unify_base
  unfold EoCases.__eo_prog_str_concat_unify_base.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_concat_unify_base x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_concat_unify_base.case_0

theorem eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_concat_unify_base x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2dchar s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_char.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_char.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2dchar
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_char.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a3 h_v1 h_v2 dropping h_a2 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_char.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v5, x_v5, h_v5⟩ else hinv1 hG in EoCases.__eo_prog_str_contains_char.case_0
  pat_unapply h_v5 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_char.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_char.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 h_v10 h_v11 dropping h_a3 h_v1 h_v3 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v1 v3 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_char.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_char.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 h_v14 h_v15 dropping h_v10 h_v11 h_v12 he_v16 hinv2 e_v16 s2 v10 v11 v12
  pat_same v14 v16 with h_v14 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_char.case_0
  pat_same v15 a0 with h_v15 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_char.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 dropping h_v14 h_v15 h_v16 hinv3 s3 v14 v15 v16
  pat_same v8 v17 with h_v8 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_contains_char.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_v2 dropping h_v17 h_v8 he_v18 hinv4 e_v18 s4 v17 v8
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2econtains.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_v2 h_v18 dropping he_v19 hinv5 e_v19 s5
  store_step with Store.apply_rep s6 v19 a0 _ _ hinv6 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_v2 h_v18 dropping h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_v2 h_v18 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v18 v21 _ _ hinv8 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_v2 dropping h_v18 h_v21 hinv8 s8 v18 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_or.construct s9 e_v23 (by rw [he_v23]; exact empty_args) hinv9 h64 as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_v2 h_v22 dropping he_v23 hinv9 e_v23 s9
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v24 (by rw [he_v24]; exact empty_args) hinv10 h64 as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_v2 h_v22 h_v23 dropping he_v24 hinv10 e_v24 s10
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_Seq.construct s11 e_v25 (by rw [he_v25]; exact empty_args) hinv11 h64 as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_v2 h_v22 h_v23 h_v24 dropping he_v25 hinv11 e_v25 s11
  store_step with Store.apply_rep s12 v25 v2 _ _ hinv12 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_v22 h_v23 h_v24 dropping h_v2 h_v25 hinv12 s12 v2 v25
  store_step with ih.eo__24seq_5fempty s13 v26 _ hinv13 h64 (hG.rem hrem) h_v26 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_v22 h_v23 h_v24 dropping h_v26 hinv13 s13 v26
  store_step with Store.apply_mk_rep s14 v24 v27 _ _ hinv14 h64 h_v24 h_v27 as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_v22 h_v23 dropping h_v24 h_v27 hinv14 s14 v24 v27
  store_step with Store.apply_mk_rep s15 v28 a1 _ _ hinv15 h64 h_v28 h_a1 as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a1 h_v22 h_v23 dropping h_v28 hinv15 s15 v28
  store_step with Store.apply_mk_rep s16 v23 v29 _ _ hinv16 h64 h_v23 h_v29 as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_a0 h_a1 h_v22 dropping h_v23 h_v29 hinv16 s16 v23 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_or.construct s17 e_v31 (by rw [he_v31]; exact empty_args) hinv17 h64 as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying h_a0 h_a1 h_v22 h_v30 dropping he_v31 hinv17 e_v31 s17
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3d.construct s18 e_v32 (by rw [he_v32]; exact empty_args) hinv18 h64 as ⟨v32, s19, hinv19, h_v32⟩ growing hG carrying h_a0 h_a1 h_v22 h_v30 h_v31 dropping he_v32 hinv18 e_v32 s18
  store_step with Store.apply_rep s19 v32 a0 _ _ hinv19 h64 h_v32 h_a0 (by ns_tac) (by ns_tac) as ⟨v33, s20, hinv20, h_v33⟩ growing hG carrying h_a1 h_v22 h_v30 h_v31 dropping h_a0 h_v32 hinv19 s19 v32
  store_step with Store.apply_rep s20 v33 a1 _ _ hinv20 h64 h_v33 h_a1 (by ns_tac) (by ns_tac) as ⟨v34, s21, hinv21, h_v34⟩ growing hG carrying h_v22 h_v30 h_v31 dropping h_a1 h_v33 hinv20 s20 v33
  store_step with Store.apply_rep s21 v31 v34 _ _ hinv21 h64 h_v31 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s22, hinv22, h_v35⟩ growing hG carrying h_v22 h_v30 dropping h_v31 h_v34 hinv21 s21 v31 v34
  store_step with Store.literal_boolean_spec s22 false hinv22 h64 as ⟨v36, s23, hinv23, h_v36⟩ growing hG carrying h_v22 h_v30 h_v35 dropping hinv22 s22
  store_step with Store.apply_rep s23 v35 v36 _ _ hinv23 h64 h_v35 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s24, hinv24, h_v37⟩ growing hG carrying h_v22 h_v30 dropping h_v35 h_v36 hinv23 s23 v35 v36
  store_step with Store.apply_mk_rep s24 v30 v37 _ _ hinv24 h64 h_v30 h_v37 as ⟨v38, s25, hinv25, h_v38⟩ growing hG carrying h_v22 dropping h_v30 h_v37 hinv24 s24 v30 v37
  store_step with Store.apply_mk_rep s25 v22 v38 _ _ hinv25 h64 h_v22 h_v38 as ⟨v39, s26, hinv26, h_v39⟩ growing hG carrying dropping h_v22 h_v38 hinv25 s25 v22 v38
  case_done hinv26 hG with h_v39 in EoCases.__eo_prog_str_contains_char.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v7 hn_v8 hn_v10 hn_v11 hn_v14 hn_v15

/-- logos's `__eo_prog_str_contains_char` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2dchar.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_contains_char x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_char.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_char
  unfold EoCases.__eo_prog_str_contains_char.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2dchar s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_char x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2dchar.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2dchar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2dchar_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_contains_char.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2dchar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2dchar.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dcontains_2dchar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2dchar s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_char x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2dchar_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2demp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_emp.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_emp.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2demp
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_contains_emp.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_emp.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_emp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_emp.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_emp.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_emp.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_emp.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_emp.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_v14 dropping he_v15 hinv4 e_v15 s4
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a1 h_v14 dropping h_a0 h_v15 hinv5 s5 v15
  store_step with Store.apply_rep s6 v16 a1 _ _ hinv6 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v14 dropping h_a1 h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v14 v17 _ _ hinv7 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying dropping h_v14 h_v17 hinv7 s7 v14 v17
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v18 dropping hinv8 s8
  store_step with Store.apply_rep s9 v18 v19 _ _ hinv9 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying dropping h_v18 h_v19 hinv9 s9 v18 v19
  case_done hinv10 hG with h_v20 in EoCases.__eo_prog_str_contains_emp.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_contains_emp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2demp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_contains_emp x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_emp.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_emp
  unfold EoCases.__eo_prog_str_contains_emp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2demp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_emp x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2demp.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2demp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2demp_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_contains_emp.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2demp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2demp.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dcontains_2demp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2demp s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_emp x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2demp_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_leq_len_eq.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_leq_len_eq.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_unapply h_v11 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v23 (by rw [he_v23]; exact empty_args) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_v4 h_v21 h_v22 dropping h_v11 h_v17 h_v18 h_v19 he_v23 hinv3 e_v23 s3 v11 v17 v18 v19
  pat_same v21 v23 with h_v21 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  pat_same v22 a0 with h_v22 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v21 h_v22 h_v23 hinv4 s4 v21 v22 v23
  pat_same v4 v24 with h_v4 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v25 (by rw [he_v25]; exact empty_args) hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 dropping h_v24 h_v4 he_v25 hinv5 e_v25 s5 v24 v4
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2econtains.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_v25 dropping he_v26 hinv6 e_v26 s6
  store_step with Store.apply_rep s7 v26 a0 _ _ hinv7 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_v25 dropping h_v26 hinv7 s7 v26
  store_step with Store.apply_rep s8 v27 a1 _ _ hinv8 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a1 h_v25 dropping h_v27 hinv8 s8 v27
  store_step with Store.apply_rep s9 v25 v28 _ _ hinv9 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a1 dropping h_v25 h_v28 hinv9 s9 v25 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v30 (by rw [he_v30]; exact empty_args) hinv10 h64 as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_a1 h_v29 dropping he_v30 hinv10 e_v30 s10
  store_step with Store.apply_rep s11 v30 a0 _ _ hinv11 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_a1 h_v29 dropping h_a0 h_v30 hinv11 s11 v30
  store_step with Store.apply_rep s12 v31 a1 _ _ hinv12 h64 h_v31 h_a1 (by ns_tac) (by ns_tac) as ⟨v32, s13, hinv13, h_v32⟩ growing hG carrying h_v29 dropping h_a1 h_v31 hinv12 s12 v31
  store_step with Store.apply_rep s13 v29 v32 _ _ hinv13 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s14, hinv14, h_v33⟩ growing hG carrying dropping h_v29 h_v32 hinv13 s13 v29 v32
  case_done hinv14 hG with h_v33 in EoCases.__eo_prog_str_contains_leq_len_eq.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v21 hn_v22

/-- logos's `__eo_prog_str_contains_leq_len_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_contains_leq_len_eq x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_leq_len_eq.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_leq_len_eq
  unfold EoCases.__eo_prog_str_contains_leq_len_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_leq_len_eq x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_contains_leq_len_eq.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_leq_len_eq x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2dleq_2dlen_2deq_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2drefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_refl.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_refl.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2drefl
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv6 s6 v4 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_str_contains_refl.case_0 using hn_a0

/-- logos's `__eo_prog_str_contains_refl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2drefl.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_contains_refl x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_refl.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_refl
  unfold EoCases.__eo_prog_str_contains_refl.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2drefl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2drefl s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_refl x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2drefl.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2drefl
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2drefl_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_contains_refl.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2drefl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2drefl.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dcontains_2drefl
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2drefl s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_refl x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2drefl_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_repl_char.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_repl_char.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_same v11 a3 with h_v11 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v20 h_v21 dropping h_a5 h_v13 h_v15 h_v17 h_v4 he_v22 hinv3 e_v22 s3 v13 v15 v17 v4
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v25 h_v27 h_v28 dropping h_v20 h_v21 h_v22 h_v24 he_v29 hinv4 e_v29 s4 v20 v21 v22 v24
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_same v28 a1 with h_v28 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 dropping h_v25 h_v27 h_v28 h_v29 hinv5 s5 v25 v27 v28 v29
  pat_same v18 v30 with h_v18 h_v30 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_contains_repl_char.case_0
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v31 (by rw [he_v31]; exact empty_args) hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v18 h_v30 he_v31 hinv6 e_v31 s6 v18 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_str_2econtains.construct s7 e_v32 (by rw [he_v32]; exact empty_args) hinv7 h64 as ⟨v32, s8, hinv8, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping he_v32 hinv7 e_v32 s7
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s8 e_v33 (by rw [he_v33]; exact empty_args) hinv8 h64 as ⟨v33, s9, hinv9, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping he_v33 hinv8 e_v33 s8
  store_step with Store.apply_rep s9 v33 a0 _ _ hinv9 h64 h_v33 h_a0 (by ns_tac) (by ns_tac) as ⟨v34, s10, hinv10, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v33 hinv9 s9 v33
  store_step with Store.apply_rep s10 v34 a1 _ _ hinv10 h64 h_v34 h_a1 (by ns_tac) (by ns_tac) as ⟨v35, s11, hinv11, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v34 hinv10 s10 v34
  store_step with Store.apply_rep s11 v35 a2 _ _ hinv11 h64 h_v35 h_a2 (by ns_tac) (by ns_tac) as ⟨v36, s12, hinv12, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v35 hinv11 s11 v35
  store_step with Store.apply_rep s12 v32 v36 _ _ hinv12 h64 h_v32 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s13, hinv13, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping h_v32 h_v36 hinv12 s12 v32 v36
  store_step with Store.apply_rep s13 v37 a3 _ _ hinv13 h64 h_v37 h_a3 (by ns_tac) (by ns_tac) as ⟨v38, s14, hinv14, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping h_v37 hinv13 s13 v37
  store_step with Store.apply_rep s14 v31 v38 _ _ hinv14 h64 h_v31 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s15, hinv15, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v31 h_v38 hinv14 s14 v31 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_or.construct s15 e_v40 (by rw [he_v40]; exact empty_args) hinv15 h64 as ⟨v40, s16, hinv16, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 dropping he_v40 hinv15 e_v40 s15
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_str_2econtains.construct s16 e_v41 (by rw [he_v41]; exact empty_args) hinv16 h64 as ⟨v41, s17, hinv17, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v40 dropping he_v41 hinv16 e_v41 s16
  store_step with Store.apply_rep s17 v41 a0 _ _ hinv17 h64 h_v41 h_a0 (by ns_tac) (by ns_tac) as ⟨v42, s18, hinv18, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v40 dropping h_v41 hinv17 s17 v41
  store_step with Store.apply_rep s18 v42 a3 _ _ hinv18 h64 h_v42 h_a3 (by ns_tac) (by ns_tac) as ⟨v43, s19, hinv19, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v40 dropping h_v42 hinv18 s18 v42
  store_step with Store.apply_rep s19 v40 v43 _ _ hinv19 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s20, hinv20, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 dropping h_v40 h_v43 hinv19 s19 v40 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_or.construct s20 e_v45 (by rw [he_v45]; exact empty_args) hinv20 h64 as ⟨v45, s21, hinv21, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v44 dropping he_v45 hinv20 e_v45 s20
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_and.construct s21 e_v46 (by rw [he_v46]; exact empty_args) hinv21 h64 as ⟨v46, s22, hinv22, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v44 h_v45 dropping he_v46 hinv21 e_v46 s21
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2econtains.construct s22 e_v47 (by rw [he_v47]; exact empty_args) hinv22 h64 as ⟨v47, s23, hinv23, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v44 h_v45 h_v46 dropping he_v47 hinv22 e_v47 s22
  store_step with Store.apply_rep s23 v47 a0 _ _ hinv23 h64 h_v47 h_a0 (by ns_tac) (by ns_tac) as ⟨v48, s24, hinv24, h_v48⟩ growing hG carrying h_a1 h_a2 h_a3 h_v39 h_v44 h_v45 h_v46 dropping h_a0 h_v47 hinv23 s23 v47
  store_step with Store.apply_rep s24 v48 a1 _ _ hinv24 h64 h_v48 h_a1 (by ns_tac) (by ns_tac) as ⟨v49, s25, hinv25, h_v49⟩ growing hG carrying h_a2 h_a3 h_v39 h_v44 h_v45 h_v46 dropping h_a1 h_v48 hinv24 s24 v48
  store_step with Store.apply_rep s25 v46 v49 _ _ hinv25 h64 h_v46 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s26, hinv26, h_v50⟩ growing hG carrying h_a2 h_a3 h_v39 h_v44 h_v45 dropping h_v46 h_v49 hinv25 s25 v46 v49
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_and.construct s26 e_v51 (by rw [he_v51]; exact empty_args) hinv26 h64 as ⟨v51, s27, hinv27, h_v51⟩ growing hG carrying h_a2 h_a3 h_v39 h_v44 h_v45 h_v50 dropping he_v51 hinv26 e_v51 s26
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo_str_2econtains.construct s27 e_v52 (by rw [he_v52]; exact empty_args) hinv27 h64 as ⟨v52, s28, hinv28, h_v52⟩ growing hG carrying h_a2 h_a3 h_v39 h_v44 h_v45 h_v50 h_v51 dropping he_v52 hinv27 e_v52 s27
  store_step with Store.apply_rep s28 v52 a2 _ _ hinv28 h64 h_v52 h_a2 (by ns_tac) (by ns_tac) as ⟨v53, s29, hinv29, h_v53⟩ growing hG carrying h_a3 h_v39 h_v44 h_v45 h_v50 h_v51 dropping h_a2 h_v52 hinv28 s28 v52
  store_step with Store.apply_rep s29 v53 a3 _ _ hinv29 h64 h_v53 h_a3 (by ns_tac) (by ns_tac) as ⟨v54, s30, hinv30, h_v54⟩ growing hG carrying h_v39 h_v44 h_v45 h_v50 h_v51 dropping h_a3 h_v53 hinv29 s29 v53
  store_step with Store.apply_rep s30 v51 v54 _ _ hinv30 h64 h_v51 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s31, hinv31, h_v55⟩ growing hG carrying h_v39 h_v44 h_v45 h_v50 dropping h_v51 h_v54 hinv30 s30 v51 v54
  store_step with Store.literal_boolean_spec s31 true hinv31 h64 as ⟨v56, s32, hinv32, h_v56⟩ growing hG carrying h_v39 h_v44 h_v45 h_v50 h_v55 dropping hinv31 s31
  store_step with Store.apply_rep s32 v55 v56 _ _ hinv32 h64 h_v55 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s33, hinv33, h_v57⟩ growing hG carrying h_v39 h_v44 h_v45 h_v50 dropping h_v55 h_v56 hinv32 s32 v55 v56
  store_step with Store.apply_rep s33 v50 v57 _ _ hinv33 h64 h_v50 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s34, hinv34, h_v58⟩ growing hG carrying h_v39 h_v44 h_v45 dropping h_v50 h_v57 hinv33 s33 v50 v57
  store_step with Store.apply_rep s34 v45 v58 _ _ hinv34 h64 h_v45 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s35, hinv35, h_v59⟩ growing hG carrying h_v39 h_v44 dropping h_v45 h_v58 hinv34 s34 v45 v58
  store_step with Store.literal_boolean_spec s35 false hinv35 h64 as ⟨v60, s36, hinv36, h_v60⟩ growing hG carrying h_v39 h_v44 h_v59 dropping hinv35 s35
  store_step with Store.apply_rep s36 v59 v60 _ _ hinv36 h64 h_v59 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s37, hinv37, h_v61⟩ growing hG carrying h_v39 h_v44 dropping h_v59 h_v60 hinv36 s36 v59 v60
  store_step with Store.apply_rep s37 v44 v61 _ _ hinv37 h64 h_v44 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s38, hinv38, h_v62⟩ growing hG carrying h_v39 dropping h_v44 h_v61 hinv37 s37 v44 v61
  store_step with Store.apply_rep s38 v39 v62 _ _ hinv38 h64 h_v39 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s39, hinv39, h_v63⟩ growing hG carrying dropping h_v39 h_v62 hinv38 s38 v39 v62
  case_done hinv39 hG with h_v63 in EoCases.__eo_prog_str_contains_repl_char.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v28

/-- logos's `__eo_prog_str_contains_repl_char` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_contains_repl_char x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_repl_char.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_repl_char
  unfold EoCases.__eo_prog_str_contains_repl_char.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_char x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_contains_repl_char.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_repl_char x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dchar_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_repl_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_repl_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v7 hinv8 s8 v0 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2econtains.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v8 dropping h_a0 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v10 a1 _ _ hinv11 h64 h_v10 h_a1 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v8 dropping h_a1 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v8 v11 _ _ hinv12 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying dropping h_v11 h_v8 hinv12 s12 v11 v8
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_str_contains_repl_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_contains_repl_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_contains_repl_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_repl_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_repl_self
  unfold EoCases.__eo_prog_str_contains_repl_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_contains_repl_self.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_repl_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping he_v15 hinv4 e_v15 s4
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with Store.apply_rep s6 v16 a0 _ _ hinv6 h64 h_v16 h_a0 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v15 dropping h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v17 a1 _ _ hinv7 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a2 h_v14 h_v15 dropping h_a1 h_v17 hinv7 s7 v17
  store_step with Store.apply_rep s8 v18 a0 _ _ hinv8 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a2 h_v14 h_v15 dropping h_v18 hinv8 s8 v18
  store_step with Store.apply_rep s9 v15 v19 _ _ hinv9 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a2 h_v14 dropping h_v15 h_v19 hinv9 s9 v15 v19
  store_step with Store.apply_rep s10 v20 a2 _ _ hinv10 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a2 h_v14 dropping h_v20 hinv10 s10 v20
  store_step with Store.apply_rep s11 v14 v21 _ _ hinv11 h64 h_v14 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a2 dropping h_v14 h_v21 hinv11 s11 v14 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_str_2econtains.construct s12 e_v23 (by rw [he_v23]; exact empty_args) hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a2 h_v22 dropping he_v23 hinv12 e_v23 s12
  store_step with Store.apply_rep s13 v23 a0 _ _ hinv13 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a2 h_v22 dropping h_a0 h_v23 hinv13 s13 v23
  store_step with Store.apply_rep s14 v24 a2 _ _ hinv14 h64 h_v24 h_a2 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_v22 dropping h_a2 h_v24 hinv14 s14 v24
  store_step with Store.apply_rep s15 v22 v25 _ _ hinv15 h64 h_v22 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying dropping h_v22 h_v25 hinv15 s15 v22 v25
  case_done hinv16 hG with h_v26 in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_contains_repl_self_tgt_char` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_contains_repl_self_tgt_char x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_repl_self_tgt_char
  unfold EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_self_tgt_char x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_contains_repl_self_tgt_char.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_repl_self_tgt_char x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dself_2dtgt_2dchar_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_repl_tgt.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_repl_tgt.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a2 _ _ hinv5 h64 h_v4 h_a2 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a2 _ _ hinv7 h64 h_v6 h_a2 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v7 hinv8 s8 v0 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v8 dropping he_v9 hinv9 e_v9 s9
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2econtains.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v8 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v8 h_v9 dropping h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a2 h_v8 h_v9 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v9 v12 _ _ hinv13 h64 h_v9 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a2 h_v8 dropping h_v12 h_v9 hinv13 s13 v12 v9
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a2 h_v8 h_v13 dropping he_v14 hinv14 e_v14 s14
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a2 h_v8 h_v13 h_v14 dropping he_v15 hinv15 e_v15 s15
  store_step with Store.apply_rep s16 v15 a0 _ _ hinv16 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a2 h_v8 h_v13 h_v14 dropping h_a0 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v16 a2 _ _ hinv17 h64 h_v16 h_a2 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v8 h_v13 h_v14 dropping h_a2 h_v16 hinv17 s17 v16
  store_step with Store.apply_rep s18 v14 v17 _ _ hinv18 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_v8 h_v13 dropping h_v14 h_v17 hinv18 s18 v14 v17
  store_step with Store.literal_boolean_spec s19 false hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_v8 h_v13 h_v18 dropping hinv19 s19
  store_step with Store.apply_rep s20 v18 v19 _ _ hinv20 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_v8 h_v13 dropping h_v18 h_v19 hinv20 s20 v18 v19
  store_step with Store.apply_rep s21 v13 v20 _ _ hinv21 h64 h_v13 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_v8 dropping h_v13 h_v20 hinv21 s21 v13 v20
  store_step with Store.apply_rep s22 v8 v21 _ _ hinv22 h64 h_v8 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying dropping h_v21 h_v8 hinv22 s22 v21 v8
  case_done hinv23 hG with h_v22 in EoCases.__eo_prog_str_contains_repl_tgt.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_str_contains_repl_tgt` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_contains_repl_tgt x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_repl_tgt.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_repl_tgt
  unfold EoCases.__eo_prog_str_contains_repl_tgt.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_repl_tgt x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_contains_repl_tgt.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_repl_tgt x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2drepl_2dtgt_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_contains_split_char.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_contains_split_char.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_contains_split_char.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_split_char.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_contains_split_char.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_split_char.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_contains_split_char.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_split_char.case_0
  pat_same v11 a3 with h_v11 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_contains_split_char.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 1#u32 (1) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_contains_split_char.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 dropping he_v15 hinv4 e_v15 s4
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with Store.apply_rep s6 v16 a0 _ _ hinv6 h64 h_v16 h_a0 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 h_v15 dropping h_v16 hinv6 s6 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 h_v15 h_v17 dropping he_v18 hinv7 e_v18 s7
  store_step with Store.apply_rep s8 v18 a1 _ _ hinv8 h64 h_v18 h_a1 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 h_v15 h_v17 dropping h_v18 hinv8 s8 v18
  store_step with Store.apply_rep s9 v19 a2 _ _ hinv9 h64 h_v19 h_a2 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 h_v15 h_v17 dropping h_v19 hinv9 s9 v19
  store_step with Store.apply_rep s10 v17 v20 _ _ hinv10 h64 h_v17 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 h_v15 dropping h_v17 h_v20 hinv10 s10 v17 v20
  store_step with Store.apply_rep s11 v15 v21 _ _ hinv11 h64 h_v15 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 dropping h_v15 h_v21 hinv11 s11 v15 v21
  store_step with Store.apply_rep s12 v22 a3 _ _ hinv12 h64 h_v22 h_a3 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v14 dropping h_v22 hinv12 s12 v22
  store_step with Store.apply_rep s13 v14 v23 _ _ hinv13 h64 h_v14 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v14 h_v23 hinv13 s13 v14 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_or.construct s14 e_v25 (by rw [he_v25]; exact empty_args) hinv14 h64 as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v24 dropping he_v25 hinv14 e_v25 s14
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2econtains.construct s15 e_v26 (by rw [he_v26]; exact empty_args) hinv15 h64 as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v24 h_v25 dropping he_v26 hinv15 e_v26 s15
  store_step with Store.apply_rep s16 v26 a0 _ _ hinv16 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 h_v25 dropping h_a0 h_v26 hinv16 s16 v26
  store_step with Store.apply_rep s17 v27 a3 _ _ hinv17 h64 h_v27 h_a3 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 h_v25 dropping h_v27 hinv17 s17 v27
  store_step with Store.apply_rep s18 v25 v28 _ _ hinv18 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 dropping h_v25 h_v28 hinv18 s18 v25 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_or.construct s19 e_v30 (by rw [he_v30]; exact empty_args) hinv19 h64 as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 h_v29 dropping he_v30 hinv19 e_v30 s19
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_str_2econtains.construct s20 e_v31 (by rw [he_v31]; exact empty_args) hinv20 h64 as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 h_v29 h_v30 dropping he_v31 hinv20 e_v31 s20
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v32 (by rw [he_v32]; exact empty_args) hinv21 h64 as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 h_v29 h_v30 h_v31 dropping he_v32 hinv21 e_v32 s21
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v33 (by rw [he_v33]; exact empty_args) hinv22 h64 as ⟨v33, s23, hinv23, h_v33⟩ growing hG carrying h_a1 h_a2 h_a3 h_v24 h_v29 h_v30 h_v31 h_v32 dropping he_v33 hinv22 e_v33 s22
  store_step with Store.apply_rep s23 v33 a1 _ _ hinv23 h64 h_v33 h_a1 (by ns_tac) (by ns_tac) as ⟨v34, s24, hinv24, h_v34⟩ growing hG carrying h_a2 h_a3 h_v24 h_v29 h_v30 h_v31 h_v32 dropping h_a1 h_v33 hinv23 s23 v33
  store_step with Store.apply_rep s24 v34 a2 _ _ hinv24 h64 h_v34 h_a2 (by ns_tac) (by ns_tac) as ⟨v35, s25, hinv25, h_v35⟩ growing hG carrying h_a3 h_v24 h_v29 h_v30 h_v31 h_v32 dropping h_a2 h_v34 hinv24 s24 v34
  step as ⟨e_v36, he_v36⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s25 e_v36 (by rw [he_v36]; rfl) h_v32 h_v35 hinv25 h64 (hG.rem hrem) op_not_left_eo_str_2e_2b_2b op_nil_apply_eo_str_2e_2b_2b as ⟨v36, s26, hinv26, h_v36⟩ growing hG carrying h_a3 h_v24 h_v29 h_v30 h_v31 dropping h_v32 h_v35 he_v36 hinv25 e_v36 s25 v32 v35
  store_step with Store.apply_mk_rep s26 v31 v36 _ _ hinv26 h64 h_v31 h_v36 as ⟨v37, s27, hinv27, h_v37⟩ growing hG carrying h_a3 h_v24 h_v29 h_v30 dropping h_v31 h_v36 hinv26 s26 v31 v36
  store_step with Store.apply_mk_rep s27 v37 a3 _ _ hinv27 h64 h_v37 h_a3 as ⟨v38, s28, hinv28, h_v38⟩ growing hG carrying h_v24 h_v29 h_v30 dropping h_a3 h_v37 hinv27 s27 v37
  store_step with Store.apply_mk_rep s28 v30 v38 _ _ hinv28 h64 h_v30 h_v38 as ⟨v39, s29, hinv29, h_v39⟩ growing hG carrying h_v24 h_v29 dropping h_v30 h_v38 hinv28 s28 v30 v38
  store_step with Store.literal_boolean_spec s29 false hinv29 h64 as ⟨v40, s30, hinv30, h_v40⟩ growing hG carrying h_v24 h_v29 h_v39 dropping hinv29 s29
  store_step with Store.apply_mk_rep s30 v39 v40 _ _ hinv30 h64 h_v39 h_v40 as ⟨v41, s31, hinv31, h_v41⟩ growing hG carrying h_v24 h_v29 dropping h_v39 h_v40 hinv30 s30 v39 v40
  store_step with Store.apply_mk_rep s31 v29 v41 _ _ hinv31 h64 h_v29 h_v41 as ⟨v42, s32, hinv32, h_v42⟩ growing hG carrying h_v24 dropping h_v29 h_v41 hinv31 s31 v29 v41
  store_step with Store.apply_mk_rep s32 v24 v42 _ _ hinv32 h64 h_v24 h_v42 as ⟨v43, s33, hinv33, h_v43⟩ growing hG carrying dropping h_v24 h_v42 hinv32 s32 v24 v42
  case_done hinv33 hG with h_v43 in EoCases.__eo_prog_str_contains_split_char.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_contains_split_char` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_contains_split_char x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_contains_split_char.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_contains_split_char
  unfold EoCases.__eo_prog_str_contains_split_char.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_contains_split_char x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_contains_split_char.case_0

theorem eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_contains_split_char x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dcontains_2dsplit_2dchar_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_ctn_full_false1.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_ctn_full_false1.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a1 h_v17 dropping h_a0 h_v18 hinv5 s5 v18
  store_step with Store.apply_rep s6 v19 a1 _ _ hinv6 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v17 dropping h_a1 h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v17 v20 _ _ hinv7 h64 h_v17 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying dropping h_v17 h_v20 hinv7 s7 v17 v20
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_v21 dropping hinv8 s8
  store_step with Store.apply_rep s9 v21 v22 _ _ hinv9 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying dropping h_v21 h_v22 hinv9 s9 v21 v22
  case_done hinv10 hG with h_v23 in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_eq_ctn_full_false1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_eq_ctn_full_false1 x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_ctn_full_false1.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_ctn_full_false1
  unfold EoCases.__eo_prog_str_eq_ctn_full_false1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_ctn_full_false1 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_eq_ctn_full_false1.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1 s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_ctn_full_false1 x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_ctn_full_false2.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_ctn_full_false2.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a1 h_v17 dropping h_a0 h_v18 hinv5 s5 v18
  store_step with Store.apply_rep s6 v19 a1 _ _ hinv6 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v17 dropping h_a1 h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v17 v20 _ _ hinv7 h64 h_v17 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying dropping h_v17 h_v20 hinv7 s7 v17 v20
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_v21 dropping hinv8 s8
  store_step with Store.apply_rep s9 v21 v22 _ _ hinv9 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying dropping h_v21 h_v22 hinv9 s9 v21 v22
  case_done hinv10 hG with h_v23 in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_eq_ctn_full_false2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_eq_ctn_full_false2 x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_ctn_full_false2.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_ctn_full_false2
  unfold EoCases.__eo_prog_str_eq_ctn_full_false2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2 s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_ctn_full_false2 x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_eq_ctn_full_false2.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2 s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_ctn_full_false2 x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_len_false.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_len_false.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_len_false.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_unapply h_v11 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v23 (by rw [he_v23]; exact empty_args) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_v4 h_v21 h_v22 dropping h_v11 h_v17 h_v18 h_v19 he_v23 hinv3 e_v23 s3 v11 v17 v18 v19
  pat_same v21 v23 with h_v21 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  pat_same v22 a1 with h_v22 h_a1 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v21 h_v22 h_v23 hinv4 s4 v21 v22 v23
  pat_same v4 v24 with h_v4 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_len_false.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v25 (by rw [he_v25]; exact empty_args) hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 dropping h_v24 h_v4 he_v25 hinv5 e_v25 s5 v24 v4
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_v25 dropping he_v26 hinv6 e_v26 s6
  store_step with Store.apply_rep s7 v26 a0 _ _ hinv7 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a1 h_v25 dropping h_a0 h_v26 hinv7 s7 v26
  store_step with Store.apply_rep s8 v27 a1 _ _ hinv8 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_v25 dropping h_a1 h_v27 hinv8 s8 v27
  store_step with Store.apply_rep s9 v25 v28 _ _ hinv9 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying dropping h_v25 h_v28 hinv9 s9 v25 v28
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_v29 dropping hinv10 s10
  store_step with Store.apply_rep s11 v29 v30 _ _ hinv11 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying dropping h_v29 h_v30 hinv11 s11 v29 v30
  case_done hinv12 hG with h_v31 in EoCases.__eo_prog_str_eq_len_false.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v21 hn_v22

/-- logos's `__eo_prog_str_eq_len_false` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_eq_len_false x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_len_false.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_len_false
  unfold EoCases.__eo_prog_str_eq_len_false.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_len_false x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_eq_len_false.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_len_false x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_same v11 a3 with h_v11 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v20 h_v21 dropping h_a5 h_v13 h_v15 h_v17 h_v4 he_v22 hinv3 e_v22 s3 v13 v15 v17 v4
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v25 h_v27 h_v28 dropping h_v20 h_v21 h_v22 h_v24 he_v29 hinv4 e_v29 s4 v20 v21 v22 v24
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 dropping h_v25 h_v27 h_v28 h_v29 hinv5 s5 v25 v27 v28 v29
  pat_same v18 v30 with h_v18 h_v30 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v31 (by rw [he_v31]; exact empty_args) hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v18 h_v30 he_v31 hinv6 e_v31 s6 v18 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v32 (by rw [he_v32]; exact empty_args) hinv7 h64 as ⟨v32, s8, hinv8, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping he_v32 hinv7 e_v32 s7
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s8 e_v33 (by rw [he_v33]; exact empty_args) hinv8 h64 as ⟨v33, s9, hinv9, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping he_v33 hinv8 e_v33 s8
  store_step with Store.apply_rep s9 v33 a0 _ _ hinv9 h64 h_v33 h_a0 (by ns_tac) (by ns_tac) as ⟨v34, s10, hinv10, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v33 hinv9 s9 v33
  store_step with Store.apply_rep s10 v34 a1 _ _ hinv10 h64 h_v34 h_a1 (by ns_tac) (by ns_tac) as ⟨v35, s11, hinv11, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v34 hinv10 s10 v34
  store_step with Store.apply_rep s11 v35 a2 _ _ hinv11 h64 h_v35 h_a2 (by ns_tac) (by ns_tac) as ⟨v36, s12, hinv12, h_v36⟩ growing hG carrying h_a0 h_a1 h_a3 h_v31 h_v32 dropping h_a2 h_v35 hinv11 s11 v35
  store_step with Store.apply_rep s12 v32 v36 _ _ hinv12 h64 h_v32 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s13, hinv13, h_v37⟩ growing hG carrying h_a0 h_a1 h_a3 h_v31 dropping h_v32 h_v36 hinv12 s12 v32 v36
  store_step with Store.apply_rep s13 v37 a3 _ _ hinv13 h64 h_v37 h_a3 (by ns_tac) (by ns_tac) as ⟨v38, s14, hinv14, h_v38⟩ growing hG carrying h_a0 h_a1 h_a3 h_v31 dropping h_v37 hinv13 s13 v37
  store_step with Store.apply_rep s14 v31 v38 _ _ hinv14 h64 h_v31 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s15, hinv15, h_v39⟩ growing hG carrying h_a0 h_a1 h_a3 dropping h_v31 h_v38 hinv14 s14 v31 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_and.construct s15 e_v40 (by rw [he_v40]; exact empty_args) hinv15 h64 as ⟨v40, s16, hinv16, h_v40⟩ growing hG carrying h_a0 h_a1 h_a3 h_v39 dropping he_v40 hinv15 e_v40 s15
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v41 (by rw [he_v41]; exact empty_args) hinv16 h64 as ⟨v41, s17, hinv17, h_v41⟩ growing hG carrying h_a0 h_a1 h_a3 h_v39 h_v40 dropping he_v41 hinv16 e_v41 s16
  store_step with Store.apply_rep s17 v41 a0 _ _ hinv17 h64 h_v41 h_a0 (by ns_tac) (by ns_tac) as ⟨v42, s18, hinv18, h_v42⟩ growing hG carrying h_a1 h_a3 h_v39 h_v40 dropping h_a0 h_v41 hinv17 s17 v41
  store_step with Store.apply_rep s18 v42 a3 _ _ hinv18 h64 h_v42 h_a3 (by ns_tac) (by ns_tac) as ⟨v43, s19, hinv19, h_v43⟩ growing hG carrying h_a1 h_a3 h_v39 h_v40 dropping h_v42 hinv18 s18 v42
  store_step with Store.apply_rep s19 v40 v43 _ _ hinv19 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s20, hinv20, h_v44⟩ growing hG carrying h_a1 h_a3 h_v39 dropping h_v40 h_v43 hinv19 s19 v40 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_and.construct s20 e_v45 (by rw [he_v45]; exact empty_args) hinv20 h64 as ⟨v45, s21, hinv21, h_v45⟩ growing hG carrying h_a1 h_a3 h_v39 h_v44 dropping he_v45 hinv20 e_v45 s20
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_not.construct s21 e_v46 (by rw [he_v46]; exact empty_args) hinv21 h64 as ⟨v46, s22, hinv22, h_v46⟩ growing hG carrying h_a1 h_a3 h_v39 h_v44 h_v45 dropping he_v46 hinv21 e_v46 s21
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__3d.construct s22 e_v47 (by rw [he_v47]; exact empty_args) hinv22 h64 as ⟨v47, s23, hinv23, h_v47⟩ growing hG carrying h_a1 h_a3 h_v39 h_v44 h_v45 h_v46 dropping he_v47 hinv22 e_v47 s22
  store_step with Store.apply_rep s23 v47 a1 _ _ hinv23 h64 h_v47 h_a1 (by ns_tac) (by ns_tac) as ⟨v48, s24, hinv24, h_v48⟩ growing hG carrying h_a3 h_v39 h_v44 h_v45 h_v46 dropping h_a1 h_v47 hinv23 s23 v47
  store_step with Store.apply_rep s24 v48 a3 _ _ hinv24 h64 h_v48 h_a3 (by ns_tac) (by ns_tac) as ⟨v49, s25, hinv25, h_v49⟩ growing hG carrying h_v39 h_v44 h_v45 h_v46 dropping h_a3 h_v48 hinv24 s24 v48
  store_step with Store.apply_rep s25 v46 v49 _ _ hinv25 h64 h_v46 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s26, hinv26, h_v50⟩ growing hG carrying h_v39 h_v44 h_v45 dropping h_v46 h_v49 hinv25 s25 v46 v49
  store_step with Store.apply_rep s26 v45 v50 _ _ hinv26 h64 h_v45 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s27, hinv27, h_v51⟩ growing hG carrying h_v39 h_v44 dropping h_v45 h_v50 hinv26 s26 v45 v50
  store_step with Store.literal_boolean_spec s27 true hinv27 h64 as ⟨v52, s28, hinv28, h_v52⟩ growing hG carrying h_v39 h_v44 h_v51 dropping hinv27 s27
  store_step with Store.apply_rep s28 v51 v52 _ _ hinv28 h64 h_v51 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s29, hinv29, h_v53⟩ growing hG carrying h_v39 h_v44 dropping h_v51 h_v52 hinv28 s28 v51 v52
  store_step with Store.apply_rep s29 v44 v53 _ _ hinv29 h64 h_v44 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s30, hinv30, h_v54⟩ growing hG carrying h_v39 dropping h_v44 h_v53 hinv29 s29 v44 v53
  store_step with Store.apply_rep s30 v39 v54 _ _ hinv30 h64 h_v39 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s31, hinv31, h_v55⟩ growing hG carrying dropping h_v39 h_v54 hinv30 s30 v39 v54
  case_done hinv31 hG with h_v55 in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v28

/-- logos's `__eo_prog_str_eq_repl_emp_tgt_nemp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_eq_repl_emp_tgt_nemp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_emp_tgt_nemp
  unfold EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_emp_tgt_nemp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_eq_repl_emp_tgt_nemp.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_emp_tgt_nemp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2demp_2dtgt_2dnemp_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v20 h_v21 dropping h_a4 h_v13 h_v15 h_v17 h_v4 he_v22 hinv3 e_v22 s3 v13 v15 v17 v4
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v24 h_v25 dropping h_v20 h_v21 h_v22 he_v26 hinv4 e_v26 s4 v20 v21 v22
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  pat_same v25 a1 with h_v25 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 dropping h_v24 h_v25 h_v26 hinv5 s5 v24 v25 v26
  pat_same v18 v27 with h_v18 h_v27 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v18 h_v27 he_v28 hinv6 e_v28 s6 v18 v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v29 (by rw [he_v29]; exact empty_args) hinv7 h64 as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v28 dropping he_v29 hinv7 e_v29 s7
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s8 e_v30 (by rw [he_v30]; exact empty_args) hinv8 h64 as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v28 h_v29 dropping he_v30 hinv8 e_v30 s8
  store_step with Store.apply_rep s9 v30 a0 _ _ hinv9 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v28 h_v29 dropping h_v30 hinv9 s9 v30
  store_step with Store.apply_rep s10 v31 a1 _ _ hinv10 h64 h_v31 h_a1 (by ns_tac) (by ns_tac) as ⟨v32, s11, hinv11, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v28 h_v29 dropping h_v31 hinv10 s10 v31
  store_step with Store.apply_rep s11 v32 a2 _ _ hinv11 h64 h_v32 h_a2 (by ns_tac) (by ns_tac) as ⟨v33, s12, hinv12, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v28 h_v29 dropping h_v32 hinv11 s11 v32
  store_step with Store.apply_rep s12 v29 v33 _ _ hinv12 h64 h_v29 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s13, hinv13, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v28 dropping h_v29 h_v33 hinv12 s12 v29 v33
  store_step with Store.apply_rep s13 v34 a2 _ _ hinv13 h64 h_v34 h_a2 (by ns_tac) (by ns_tac) as ⟨v35, s14, hinv14, h_v35⟩ growing hG carrying h_a0 h_a1 h_v28 dropping h_a2 h_v34 hinv13 s13 v34
  store_step with Store.apply_rep s14 v28 v35 _ _ hinv14 h64 h_v28 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s15, hinv15, h_v36⟩ growing hG carrying h_a0 h_a1 dropping h_v28 h_v35 hinv14 s14 v28 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2eprefixof.construct s15 e_v37 (by rw [he_v37]; exact empty_args) hinv15 h64 as ⟨v37, s16, hinv16, h_v37⟩ growing hG carrying h_a0 h_a1 h_v36 dropping he_v37 hinv15 e_v37 s15
  store_step with Store.apply_rep s16 v37 a0 _ _ hinv16 h64 h_v37 h_a0 (by ns_tac) (by ns_tac) as ⟨v38, s17, hinv17, h_v38⟩ growing hG carrying h_a1 h_v36 dropping h_a0 h_v37 hinv16 s16 v37
  store_step with Store.apply_rep s17 v38 a1 _ _ hinv17 h64 h_v38 h_a1 (by ns_tac) (by ns_tac) as ⟨v39, s18, hinv18, h_v39⟩ growing hG carrying h_v36 dropping h_a1 h_v38 hinv17 s17 v38
  store_step with Store.apply_rep s18 v36 v39 _ _ hinv18 h64 h_v36 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s19, hinv19, h_v40⟩ growing hG carrying dropping h_v36 h_v39 hinv18 s18 v36 v39
  case_done hinv19 hG with h_v40 in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25

/-- logos's `__eo_prog_str_eq_repl_len_one_emp_prefix` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_eq_repl_len_one_emp_prefix x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_len_one_emp_prefix
  unfold EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_len_one_emp_prefix x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_eq_repl_len_one_emp_prefix.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_len_one_emp_prefix x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dlen_2done_2demp_2dprefix_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_same v11 a3 with h_v11 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v20 h_v21 dropping h_a5 h_v13 h_v15 h_v17 h_v4 he_v22 hinv3 e_v22 s3 v13 v15 v17 v4
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 h_v25 h_v27 h_v28 dropping h_v20 h_v21 h_v22 h_v24 he_v29 hinv4 e_v29 s4 v20 v21 v22 v24
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v18 dropping h_v25 h_v27 h_v28 h_v29 hinv5 s5 v25 v27 v28 v29
  pat_same v18 v30 with h_v18 h_v30 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v31 (by rw [he_v31]; exact empty_args) hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v18 h_v30 he_v31 hinv6 e_v31 s6 v18 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v32 (by rw [he_v32]; exact empty_args) hinv7 h64 as ⟨v32, s8, hinv8, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping he_v32 hinv7 e_v32 s7
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s8 e_v33 (by rw [he_v33]; exact empty_args) hinv8 h64 as ⟨v33, s9, hinv9, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping he_v33 hinv8 e_v33 s8
  store_step with Store.apply_rep s9 v33 a3 _ _ hinv9 h64 h_v33 h_a3 (by ns_tac) (by ns_tac) as ⟨v34, s10, hinv10, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v33 hinv9 s9 v33
  store_step with Store.apply_rep s10 v34 a0 _ _ hinv10 h64 h_v34 h_a0 (by ns_tac) (by ns_tac) as ⟨v35, s11, hinv11, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v34 hinv10 s10 v34
  store_step with Store.apply_rep s11 v35 a1 _ _ hinv11 h64 h_v35 h_a1 (by ns_tac) (by ns_tac) as ⟨v36, s12, hinv12, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 h_v32 dropping h_v35 hinv11 s11 v35
  store_step with Store.apply_rep s12 v32 v36 _ _ hinv12 h64 h_v32 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s13, hinv13, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping h_v32 h_v36 hinv12 s12 v32 v36
  store_step with Store.apply_rep s13 v37 a2 _ _ hinv13 h64 h_v37 h_a2 (by ns_tac) (by ns_tac) as ⟨v38, s14, hinv14, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v31 dropping h_v37 hinv13 s13 v37
  store_step with Store.apply_rep s14 v31 v38 _ _ hinv14 h64 h_v31 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s15, hinv15, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v31 h_v38 hinv14 s14 v31 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_and.construct s15 e_v40 (by rw [he_v40]; exact empty_args) hinv15 h64 as ⟨v40, s16, hinv16, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 dropping he_v40 hinv15 e_v40 s15
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v41 (by rw [he_v41]; exact empty_args) hinv16 h64 as ⟨v41, s17, hinv17, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v39 h_v40 dropping he_v41 hinv16 e_v41 s16
  store_step with Store.apply_rep s17 v41 a0 _ _ hinv17 h64 h_v41 h_a0 (by ns_tac) (by ns_tac) as ⟨v42, s18, hinv18, h_v42⟩ growing hG carrying h_a1 h_a2 h_a3 h_v39 h_v40 dropping h_a0 h_v41 hinv17 s17 v41
  store_step with Store.apply_rep s18 v42 a3 _ _ hinv18 h64 h_v42 h_a3 (by ns_tac) (by ns_tac) as ⟨v43, s19, hinv19, h_v43⟩ growing hG carrying h_a1 h_a2 h_v39 h_v40 dropping h_a3 h_v42 hinv18 s18 v42
  store_step with Store.apply_rep s19 v40 v43 _ _ hinv19 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s20, hinv20, h_v44⟩ growing hG carrying h_a1 h_a2 h_v39 dropping h_v40 h_v43 hinv19 s19 v40 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_and.construct s20 e_v45 (by rw [he_v45]; exact empty_args) hinv20 h64 as ⟨v45, s21, hinv21, h_v45⟩ growing hG carrying h_a1 h_a2 h_v39 h_v44 dropping he_v45 hinv20 e_v45 s20
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__3d.construct s21 e_v46 (by rw [he_v46]; exact empty_args) hinv21 h64 as ⟨v46, s22, hinv22, h_v46⟩ growing hG carrying h_a1 h_a2 h_v39 h_v44 h_v45 dropping he_v46 hinv21 e_v46 s21
  store_step with Store.apply_rep s22 v46 a1 _ _ hinv22 h64 h_v46 h_a1 (by ns_tac) (by ns_tac) as ⟨v47, s23, hinv23, h_v47⟩ growing hG carrying h_a2 h_v39 h_v44 h_v45 dropping h_a1 h_v46 hinv22 s22 v46
  store_step with Store.apply_rep s23 v47 a2 _ _ hinv23 h64 h_v47 h_a2 (by ns_tac) (by ns_tac) as ⟨v48, s24, hinv24, h_v48⟩ growing hG carrying h_v39 h_v44 h_v45 dropping h_a2 h_v47 hinv23 s23 v47
  store_step with Store.apply_rep s24 v45 v48 _ _ hinv24 h64 h_v45 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s25, hinv25, h_v49⟩ growing hG carrying h_v39 h_v44 dropping h_v45 h_v48 hinv24 s24 v45 v48
  store_step with Store.literal_boolean_spec s25 true hinv25 h64 as ⟨v50, s26, hinv26, h_v50⟩ growing hG carrying h_v39 h_v44 h_v49 dropping hinv25 s25
  store_step with Store.apply_rep s26 v49 v50 _ _ hinv26 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s27, hinv27, h_v51⟩ growing hG carrying h_v39 h_v44 dropping h_v49 h_v50 hinv26 s26 v49 v50
  store_step with Store.apply_rep s27 v44 v51 _ _ hinv27 h64 h_v44 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s28, hinv28, h_v52⟩ growing hG carrying h_v39 dropping h_v44 h_v51 hinv27 s27 v44 v51
  store_step with Store.apply_rep s28 v39 v52 _ _ hinv28 h64 h_v39 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s29, hinv29, h_v53⟩ growing hG carrying dropping h_v39 h_v52 hinv28 s28 v39 v52
  case_done hinv29 hG with h_v53 in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v28

/-- logos's `__eo_prog_str_eq_repl_nemp_src_emp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_eq_repl_nemp_src_emp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_nemp_src_emp
  unfold EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_nemp_src_emp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_eq_repl_nemp_src_emp.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_nemp_src_emp x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dnemp_2dsrc_2demp_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_no_change.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_no_change.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_no_change.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping he_v19 hinv5 e_v19 s5
  store_step with Store.apply_rep s6 v19 a0 _ _ hinv6 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v21 a2 _ _ hinv8 h64 h_v21 h_a2 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 dropping h_a2 h_v21 hinv8 s8 v21
  store_step with Store.apply_rep s9 v18 v22 _ _ hinv9 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_v17 dropping h_v18 h_v22 hinv9 s9 v18 v22
  store_step with Store.apply_rep s10 v23 a0 _ _ hinv10 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_v17 dropping h_v23 hinv10 s10 v23
  store_step with Store.apply_rep s11 v17 v24 _ _ hinv11 h64 h_v17 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 dropping h_v17 h_v24 hinv11 s11 v17 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_not.construct s12 e_v26 (by rw [he_v26]; exact empty_args) hinv12 h64 as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_v25 dropping he_v26 hinv12 e_v26 s12
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2econtains.construct s13 e_v27 (by rw [he_v27]; exact empty_args) hinv13 h64 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_v25 h_v26 dropping he_v27 hinv13 e_v27 s13
  store_step with Store.apply_rep s14 v27 a0 _ _ hinv14 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a1 h_v25 h_v26 dropping h_a0 h_v27 hinv14 s14 v27
  store_step with Store.apply_rep s15 v28 a1 _ _ hinv15 h64 h_v28 h_a1 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_v25 h_v26 dropping h_a1 h_v28 hinv15 s15 v28
  store_step with Store.apply_rep s16 v26 v29 _ _ hinv16 h64 h_v26 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_v25 dropping h_v26 h_v29 hinv16 s16 v26 v29
  store_step with Store.apply_rep s17 v25 v30 _ _ hinv17 h64 h_v25 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying dropping h_v25 h_v30 hinv17 s17 v25 v30
  case_done hinv18 hG with h_v31 in EoCases.__eo_prog_str_eq_repl_no_change.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_eq_repl_no_change` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_eq_repl_no_change x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_no_change.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_no_change
  unfold EoCases.__eo_prog_str_eq_repl_no_change.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_no_change x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_eq_repl_no_change.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_no_change x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dno_2dchange_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_self_emp.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_self_emp.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping he_v15 hinv4 e_v15 s4
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with Store.apply_rep s6 v16 a0 _ _ hinv6 h64 h_v16 h_a0 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v15 dropping h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v17 a1 _ _ hinv7 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a2 h_v14 h_v15 dropping h_a1 h_v17 hinv7 s7 v17
  store_step with Store.apply_rep s8 v18 a0 _ _ hinv8 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a2 h_v14 h_v15 dropping h_v18 hinv8 s8 v18
  store_step with Store.apply_rep s9 v15 v19 _ _ hinv9 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a2 h_v14 dropping h_v15 h_v19 hinv9 s9 v15 v19
  store_step with Store.apply_rep s10 v20 a2 _ _ hinv10 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a2 h_v14 dropping h_v20 hinv10 s10 v20
  store_step with Store.apply_rep s11 v14 v21 _ _ hinv11 h64 h_v14 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a2 dropping h_v14 h_v21 hinv11 s11 v14 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v23 (by rw [he_v23]; exact empty_args) hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a2 h_v22 dropping he_v23 hinv12 e_v23 s12
  store_step with Store.apply_rep s13 v23 a0 _ _ hinv13 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a2 h_v22 dropping h_a0 h_v23 hinv13 s13 v23
  store_step with Store.apply_rep s14 v24 a2 _ _ hinv14 h64 h_v24 h_a2 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_v22 dropping h_a2 h_v24 hinv14 s14 v24
  store_step with Store.apply_rep s15 v22 v25 _ _ hinv15 h64 h_v22 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying dropping h_v22 h_v25 hinv15 s15 v22 v25
  case_done hinv16 hG with h_v26 in EoCases.__eo_prog_str_eq_repl_self_emp.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_eq_repl_self_emp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_eq_repl_self_emp x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_self_emp.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_self_emp
  unfold EoCases.__eo_prog_str_eq_repl_self_emp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_self_emp x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_eq_repl_self_emp.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_self_emp x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2demp_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_self_src.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_self_src.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v1 v5 _ _ hinv6 h64 h_v1 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v5 hinv6 s6 v1 v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v7 hinv8 s8 v0 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v8 dropping h_a0 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v10 a1 _ _ hinv11 h64 h_v10 h_a1 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v8 dropping h_a1 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v8 v11 _ _ hinv12 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying dropping h_v11 h_v8 hinv12 s12 v11 v8
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_str_eq_repl_self_src.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_eq_repl_self_src` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_eq_repl_self_src x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_self_src.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_self_src
  unfold EoCases.__eo_prog_str_eq_repl_self_src.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_self_src x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_eq_repl_self_src.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_self_src x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dself_2dsrc_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  pat_unapply h_v4 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v15 dropping h_v10 h_v11 h_v12 h_v4 he_v16 hinv2 e_v16 s2 v10 v11 v12 v4
  pat_same v14 v16 with h_v14 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  pat_same v15 a2 with h_v15 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v14 h_v15 h_v16 he_v17 hinv3 e_v17 s3 v14 v15 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping he_v19 hinv5 e_v19 s5
  store_step with Store.apply_rep s6 v19 a0 _ _ hinv6 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v21 a2 _ _ hinv8 h64 h_v21 h_a2 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v18 dropping h_v21 hinv8 s8 v21
  store_step with Store.apply_rep s9 v18 v22 _ _ hinv9 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 h_v22 hinv9 s9 v18 v22
  store_step with Store.apply_rep s10 v23 a2 _ _ hinv10 h64 h_v23 h_a2 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v23 hinv10 s10 v23
  store_step with Store.apply_rep s11 v17 v24 _ _ hinv11 h64 h_v17 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v17 h_v24 hinv11 s11 v17 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_or.construct s12 e_v26 (by rw [he_v26]; exact empty_args) hinv12 h64 as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping he_v26 hinv12 e_v26 s12
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s13 e_v27 (by rw [he_v27]; exact empty_args) hinv13 h64 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping he_v27 hinv13 e_v27 s13
  store_step with Store.apply_rep s14 v27 a0 _ _ hinv14 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v27 hinv14 s14 v27
  store_step with Store.apply_rep s15 v28 a1 _ _ hinv15 h64 h_v28 h_a1 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a2 h_v25 h_v26 dropping h_a1 h_v28 hinv15 s15 v28
  store_step with Store.apply_rep s16 v26 v29 _ _ hinv16 h64 h_v26 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_a0 h_a2 h_v25 dropping h_v26 h_v29 hinv16 s16 v26 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_or.construct s17 e_v31 (by rw [he_v31]; exact empty_args) hinv17 h64 as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying h_a0 h_a2 h_v25 h_v30 dropping he_v31 hinv17 e_v31 s17
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3d.construct s18 e_v32 (by rw [he_v32]; exact empty_args) hinv18 h64 as ⟨v32, s19, hinv19, h_v32⟩ growing hG carrying h_a0 h_a2 h_v25 h_v30 h_v31 dropping he_v32 hinv18 e_v32 s18
  store_step with Store.apply_rep s19 v32 a0 _ _ hinv19 h64 h_v32 h_a0 (by ns_tac) (by ns_tac) as ⟨v33, s20, hinv20, h_v33⟩ growing hG carrying h_a2 h_v25 h_v30 h_v31 dropping h_a0 h_v32 hinv19 s19 v32
  store_step with Store.apply_rep s20 v33 a2 _ _ hinv20 h64 h_v33 h_a2 (by ns_tac) (by ns_tac) as ⟨v34, s21, hinv21, h_v34⟩ growing hG carrying h_v25 h_v30 h_v31 dropping h_a2 h_v33 hinv20 s20 v33
  store_step with Store.apply_rep s21 v31 v34 _ _ hinv21 h64 h_v31 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s22, hinv22, h_v35⟩ growing hG carrying h_v25 h_v30 dropping h_v31 h_v34 hinv21 s21 v31 v34
  store_step with Store.literal_boolean_spec s22 false hinv22 h64 as ⟨v36, s23, hinv23, h_v36⟩ growing hG carrying h_v25 h_v30 h_v35 dropping hinv22 s22
  store_step with Store.apply_rep s23 v35 v36 _ _ hinv23 h64 h_v35 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s24, hinv24, h_v37⟩ growing hG carrying h_v25 h_v30 dropping h_v35 h_v36 hinv23 s23 v35 v36
  store_step with Store.apply_rep s24 v30 v37 _ _ hinv24 h64 h_v30 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s25, hinv25, h_v38⟩ growing hG carrying h_v25 dropping h_v30 h_v37 hinv24 s24 v30 v37
  store_step with Store.apply_rep s25 v25 v38 _ _ hinv25 h64 h_v25 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s26, hinv26, h_v39⟩ growing hG carrying dropping h_v25 h_v38 hinv25 s25 v25 v38
  case_done hinv26 hG with h_v39 in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15

/-- logos's `__eo_prog_str_eq_repl_tgt_eq_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_eq_repl_tgt_eq_len x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_eq_repl_tgt_eq_len
  unfold EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_eq_repl_tgt_eq_len x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_eq_repl_tgt_eq_len.case_0

theorem eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_eq_repl_tgt_eq_len x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2deq_2drepl_2dtgt_2deq_2dlen_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a3 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a3 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a3 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_v22 h_v24 h_v25 dropping h_a3 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s5 e_v30 (by rw [he_v30]; exact empty_args) hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_a1 h_v22 h_v28 h_v29 dropping h_v24 h_v25 h_v26 he_v30 hinv5 e_v30 s5 v24 v25 v26
  pat_same v28 v30 with h_v28 h_v30 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  pat_same v29 a1 with h_v29 h_a1 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s6 1#u32 (-1) (by scalar_tac) hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_a1 h_v22 dropping h_v28 h_v29 h_v30 hinv6 s6 v28 v29 v30
  pat_same v22 v31 with h_v22 h_v31 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v32 (by rw [he_v32]; exact empty_args) hinv7 h64 as ⟨v32, s8, hinv8, h_v32⟩ growing hG carrying h_a0 h_a1 dropping h_v22 h_v31 he_v32 hinv7 e_v32 s7 v22 v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_str_2econtains.construct s8 e_v33 (by rw [he_v33]; exact empty_args) hinv8 h64 as ⟨v33, s9, hinv9, h_v33⟩ growing hG carrying h_a0 h_a1 h_v32 dropping he_v33 hinv8 e_v33 s8
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s9 e_v34 (by rw [he_v34]; exact empty_args) hinv9 h64 as ⟨v34, s10, hinv10, h_v34⟩ growing hG carrying h_a0 h_a1 h_v32 h_v33 dropping he_v34 hinv9 e_v34 s9
  store_step with Store.apply_rep s10 v34 a0 _ _ hinv10 h64 h_v34 h_a0 (by ns_tac) (by ns_tac) as ⟨v35, s11, hinv11, h_v35⟩ growing hG carrying h_a1 h_v32 h_v33 dropping h_a0 h_v34 hinv10 s10 v34
  store_step with Store.apply_rep s11 v33 v35 _ _ hinv11 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s12, hinv12, h_v36⟩ growing hG carrying h_a1 h_v32 dropping h_v33 h_v35 hinv11 s11 v33 v35
  store_step with Store.apply_rep s12 v36 a1 _ _ hinv12 h64 h_v36 h_a1 (by ns_tac) (by ns_tac) as ⟨v37, s13, hinv13, h_v37⟩ growing hG carrying h_v32 dropping h_a1 h_v36 hinv12 s12 v36
  store_step with Store.apply_rep s13 v32 v37 _ _ hinv13 h64 h_v32 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s14, hinv14, h_v38⟩ growing hG carrying dropping h_v32 h_v37 hinv13 s13 v32 v37
  store_step with Store.literal_boolean_spec s14 false hinv14 h64 as ⟨v39, s15, hinv15, h_v39⟩ growing hG carrying h_v38 dropping hinv14 s14
  store_step with Store.apply_rep s15 v38 v39 _ _ hinv15 h64 h_v38 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s16, hinv16, h_v40⟩ growing hG carrying dropping h_v38 h_v39 hinv15 s15 v38 v39
  case_done hinv16 hG with h_v40 in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29

/-- logos's `__eo_prog_str_from_int_no_ctn_nondigit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_from_int_no_ctn_nondigit x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_from_int_no_ctn_nondigit
  unfold EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_from_int_no_ctn_nondigit x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_from_int_no_ctn_nondigit.case_0

theorem eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_from_int_no_ctn_nondigit x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dfrom_2dint_2dno_2dctn_2dnondigit_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_in_re_concat_star_char.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_in_re_concat_star_char.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_v2 h_v9 h_v16 h_v18 h_v19 dropping h_v11 h_v12 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v12 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  pat_unapply h_v9 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s3 e_v24 (by rw [he_v24]; exact empty_args) hinv3 h64 as ⟨v24, s4, hinv4, h_v24⟩ growing hG carrying h_v2 h_v16 h_v19 h_v22 h_v23 dropping h_v18 h_v20 h_v9 he_v24 hinv3 e_v24 s3 v18 v20 v9
  pat_same v22 v24 with h_v22 h_v24 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  store_step with ih.eo__24str_5ffixed_5flen_5fre s4 v23 _ hinv4 h64 (hG.rem hrem) h_v23 as ⟨v25, s5, hinv5, h_v25⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 dropping h_v22 h_v24 hinv4 s4 v22 v24
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v26, s6, hinv6, h_v26⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 h_v25 dropping hinv5 s5
  have h_req_v45 := (show requires_1_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar s6 v25 v26 v19 v16 v23 v2 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v25 v26 with h_v25 h_v26 using hinv6 hG
    req_stuck h_v25 as hq_v25 using hinv6 hG
    step as ⟨e_v27, he_v27⟩
    store_step with CtorSpec.eo_str_2e_2b_2b.construct s6 e_v27 (by rw [he_v27]; exact empty_args) hinv6 h64 as ⟨v27, s7, hinv7, h_v27⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 dropping h_v25 h_v26 he_v27 hinv6 e_v27 s6 v25 v26
    store_step with Store.apply_rep s7 v27 v19 _ _ hinv7 h64 h_v27 h_v19 (by ns_tac) (by ns_tac) as ⟨v28, s8, hinv8, h_v28⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 dropping h_v27 hinv7 s7 v27
    store_step with Store.apply_rep s8 v28 v16 _ _ hinv8 h64 h_v28 h_v16 (by ns_tac) (by ns_tac) as ⟨v29, s9, hinv9, h_v29⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 dropping h_v28 hinv8 s8 v28
    step as ⟨e_v30, he_v30⟩
    store_step with CtorSpec.eo_re_2e_2a.construct s9 e_v30 (by rw [he_v30]; exact empty_args) hinv9 h64 as ⟨v30, s10, hinv10, h_v30⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 h_v29 dropping he_v30 hinv9 e_v30 s9
    store_step with Store.apply_rep s10 v30 v23 _ _ hinv10 h64 h_v30 h_v23 (by ns_tac) (by ns_tac) as ⟨v31, s11, hinv11, h_v31⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 h_v29 dropping h_v30 hinv10 s10 v30
    store_step with ih.eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar s11 v29 v31 _ _ hinv11 h64 (hG.rem hrem) h_v29 h_v31 as ⟨v32, s12, hinv12, h_v32⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 dropping h_v29 h_v31 hinv11 s11 v29 v31
    have h_req_v44 := (show requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar s12 v32 v2 v19 v16 v23 ⦃ r s' => s'.Inv ∧ s12.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s12
      req_same v32 v2 with h_v32 h_v2 using hinv12 hG
      req_stuck h_v32 as hq_v32 using hinv12 hG
      step as ⟨e_v33, he_v33⟩
      store_step with CtorSpec.eo__3d.construct s12 e_v33 (by rw [he_v33]; exact empty_args) hinv12 h64 as ⟨v33, s13, hinv13, h_v33⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 dropping h_v32 he_v33 hinv12 e_v33 s12 v32
      step as ⟨e_v34, he_v34⟩
      store_step with CtorSpec.eo_str_2ein_5fre.construct s13 e_v34 (by rw [he_v34]; exact empty_args) hinv13 h64 as ⟨v34, s14, hinv14, h_v34⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 h_v33 dropping he_v34 hinv13 e_v34 s13
      step as ⟨e_v35, he_v35⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v35 (by rw [he_v35]; exact empty_args) hinv14 h64 as ⟨v35, s15, hinv15, h_v35⟩ growing hG carrying h_v2 h_v16 h_v19 h_v23 h_v33 h_v34 dropping he_v35 hinv14 e_v35 s14
      store_step with Store.apply_rep s15 v35 v19 _ _ hinv15 h64 h_v35 h_v19 (by ns_tac) (by ns_tac) as ⟨v36, s16, hinv16, h_v36⟩ growing hG carrying h_v2 h_v16 h_v23 h_v33 h_v34 dropping h_v19 h_v35 hinv15 s15 v19 v35
      store_step with Store.apply_rep s16 v36 v16 _ _ hinv16 h64 h_v36 h_v16 (by ns_tac) (by ns_tac) as ⟨v37, s17, hinv17, h_v37⟩ growing hG carrying h_v2 h_v23 h_v33 h_v34 dropping h_v16 h_v36 hinv16 s16 v16 v36
      store_step with Store.apply_rep s17 v34 v37 _ _ hinv17 h64 h_v34 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s18, hinv18, h_v38⟩ growing hG carrying h_v2 h_v23 h_v33 dropping h_v34 h_v37 hinv17 s17 v34 v37
      step as ⟨e_v39, he_v39⟩
      store_step with CtorSpec.eo_re_2e_2a.construct s18 e_v39 (by rw [he_v39]; exact empty_args) hinv18 h64 as ⟨v39, s19, hinv19, h_v39⟩ growing hG carrying h_v2 h_v23 h_v33 h_v38 dropping he_v39 hinv18 e_v39 s18
      store_step with Store.apply_rep s19 v39 v23 _ _ hinv19 h64 h_v39 h_v23 (by ns_tac) (by ns_tac) as ⟨v40, s20, hinv20, h_v40⟩ growing hG carrying h_v2 h_v33 h_v38 dropping h_v23 h_v39 hinv19 s19 v23 v39
      store_step with Store.apply_rep s20 v38 v40 _ _ hinv20 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s21, hinv21, h_v41⟩ growing hG carrying h_v2 h_v33 dropping h_v38 h_v40 hinv20 s20 v38 v40
      store_step with Store.apply_rep s21 v33 v41 _ _ hinv21 h64 h_v33 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s22, hinv22, h_v42⟩ growing hG carrying h_v2 dropping h_v33 h_v41 hinv21 s21 v33 v41
      store_step with Store.apply_rep s22 v42 v2 _ _ hinv22 h64 h_v42 h_v2 (by ns_tac) (by ns_tac) as ⟨v43, s23, hinv23, h_v43⟩ growing hG carrying dropping h_v2 h_v42 hinv22 s22 v2 v42
      req_done hinv23 hG with h_v43 using hq_v32)
    store_step with h_req_v44 as ⟨v44, s24, hinv24, h_v44⟩ growing hG carrying dropping h_req_v44 h_v16 h_v19 h_v2 h_v23 h_v32 hinv12 s12 v16 v19 v2 v23 v32
    req_done hinv24 hG with h_v44 using hq_v25)
  store_step with h_req_v45 as ⟨v45, s25, hinv25, h_v45⟩ growing hG carrying dropping h_req_v45 h_v16 h_v19 h_v2 h_v23 h_v25 h_v26 hinv6 s6 v16 v19 v2 v23 v25 v26
  case_done hinv25 hG with h_v45 in EoCases.__eo_prog_str_in_re_concat_star_char.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19 hn_v22 hn_v23

/-- logos's `__eo_prog_str_in_re_concat_star_char` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_in_re_concat_star_char x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_in_re_concat_star_char.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_in_re_concat_star_char
  unfold EoCases.__eo_prog_str_in_re_concat_star_char.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_concat_star_char x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_in_re_concat_star_char.case_0

theorem eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_in_re_concat_star_char x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_in_re_contains.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_in_re_contains.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 dropping he_v4 hinv4 e_v4 s4
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 dropping h_v4 h_v5 hinv6 s6 v4 v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v3 h_v6 hinv7 s7 v3 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 dropping he_v8 hinv8 e_v8 s8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v8 dropping h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 dropping h_v10 h_v8 hinv11 s11 v10 v8
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 dropping he_v12 hinv12 e_v12 s12
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 h_v12 dropping he_v13 hinv13 e_v13 s13
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 h_v12 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v13 v14 _ _ hinv15 h64 h_v13 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 h_v12 dropping h_v13 h_v14 hinv15 s15 v13 v14
  store_step with Store.apply_rep s16 v12 v15 _ _ hinv16 h64 h_v12 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 dropping h_v12 h_v15 hinv16 s16 v12 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 h_v16 dropping he_v17 hinv17 e_v17 s17
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s18 _ _ rfl hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 h_v16 h_v17 dropping hinv18 s18
  store_step with Store.apply_rep s19 v17 v18 _ _ hinv19 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 h_v16 dropping h_v17 h_v18 hinv19 s19 v17 v18
  store_step with Store.apply_rep s20 v16 v19 _ _ hinv20 h64 h_v16 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 h_v11 dropping h_v16 h_v19 hinv20 s20 v16 v19
  store_step with Store.apply_rep s21 v11 v20 _ _ hinv21 h64 h_v11 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v7 dropping h_v11 h_v20 hinv21 s21 v11 v20
  store_step with Store.apply_rep s22 v7 v21 _ _ hinv22 h64 h_v7 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v21 h_v7 hinv22 s22 v21 v7
  store_step with Store.apply_rep s23 v2 v22 _ _ hinv23 h64 h_v2 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v22 hinv23 s23 v2 v22
  store_step with Store.apply_rep s24 v0 v23 _ _ hinv24 h64 h_v0 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v23 hinv24 s24 v0 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2econtains.construct s25 e_v25 (by rw [he_v25]; exact empty_args) hinv25 h64 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_v24 dropping he_v25 hinv25 e_v25 s25
  store_step with Store.apply_rep s26 v25 a0 _ _ hinv26 h64 h_v25 h_a0 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a1 h_v24 dropping h_a0 h_v25 hinv26 s26 v25
  store_step with Store.apply_rep s27 v26 a1 _ _ hinv27 h64 h_v26 h_a1 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_v24 dropping h_a1 h_v26 hinv27 s27 v26
  store_step with Store.apply_rep s28 v24 v27 _ _ hinv28 h64 h_v24 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying dropping h_v24 h_v27 hinv28 s28 v24 v27
  case_done hinv29 hG with h_v28 in EoCases.__eo_prog_str_in_re_contains.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_in_re_contains` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2din_2dre_2dcontains.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_in_re_contains x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_in_re_contains.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_in_re_contains
  unfold EoCases.__eo_prog_str_in_re_contains.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_contains x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2din_2dre_2dcontains.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_in_re_contains.case_0

theorem eo__24eo_5fprog_5fstr_2din_2dre_2dcontains_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2din_2dre_2dcontains.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2din_2dre_2dcontains
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_in_re_contains x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2din_2dre_2dcontains_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_in_re_from_int_dig_range.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_in_re_from_int_dig_range.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 h_v1 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v0 dropping h_v1 h_v3 hinv4 s4 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v0 h_v4 dropping he_v5 hinv5 e_v5 s5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2erange.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v0 h_v4 h_v5 dropping he_v6 hinv6 e_v6 s6
  step as ⟨e_v7, he_v7⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s7 _ _ rfl hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v0 h_v4 h_v5 h_v6 dropping hinv7 s7
  replace h_v7 := Represents.rep_of_eq h_v7 (y := Eo.Term.String (SmtEval.native_string_lit "0")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v7]; decide)
  store_step with Store.apply_rep s8 v6 v7 _ _ hinv8 h64 h_v6 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v0 h_v4 h_v5 dropping h_v6 h_v7 he_v7 hinv8 e_v7 s8 v6 v7
  step as ⟨e_v9, he_v9⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s9 _ _ rfl hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v0 h_v4 h_v5 h_v8 dropping hinv9 s9
  replace h_v9 := Represents.rep_of_eq h_v9 (y := Eo.Term.String (SmtEval.native_string_lit "9")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v9]; decide)
  store_step with Store.apply_rep s10 v8 v9 _ _ hinv10 h64 h_v8 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v0 h_v4 h_v5 dropping h_v8 h_v9 he_v9 hinv10 e_v9 s10 v8 v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v0 h_v4 dropping h_v10 h_v5 hinv11 s11 v10 v5
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v0 dropping h_v11 h_v4 hinv12 s12 v11 v4
  store_step with Store.apply_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying dropping h_v0 h_v12 hinv13 s13 v0 v12
  store_step with Store.literal_boolean_spec s14 true hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_v13 dropping hinv14 s14
  store_step with Store.apply_rep s15 v13 v14 _ _ hinv15 h64 h_v13 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying dropping h_v13 h_v14 hinv15 s15 v13 v14
  case_done hinv16 hG with h_v15 in EoCases.__eo_prog_str_in_re_from_int_dig_range.case_0 using hn_a0

/-- logos's `__eo_prog_str_in_re_from_int_dig_range` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_in_re_from_int_dig_range x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_in_re_from_int_dig_range.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_in_re_from_int_dig_range
  unfold EoCases.__eo_prog_str_in_re_from_int_dig_range.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_from_int_dig_range x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_in_re_from_int_dig_range.case_0

theorem eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_in_re_from_int_dig_range x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2ddig_2drange_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v4 h_v6 h_v7 dropping h_a1 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 dropping h_v17 h_v4 he_v18 hinv4 e_v18 s4 v17 v4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v18 dropping he_v19 hinv5 e_v19 s5
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_v18 h_v19 dropping he_v20 hinv6 e_v20 s6
  store_step with Store.apply_rep s7 v20 a0 _ _ hinv7 h64 h_v20 h_a0 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_v18 h_v19 dropping h_a0 h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v19 v21 _ _ hinv8 h64 h_v19 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_v18 dropping h_v19 h_v21 hinv8 s8 v19 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s9 e_v23 (by rw [he_v23]; exact empty_args) hinv9 h64 as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_v18 h_v22 dropping he_v23 hinv9 e_v23 s9
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_re_2erange.construct s10 e_v24 (by rw [he_v24]; exact empty_args) hinv10 h64 as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_v18 h_v22 h_v23 dropping he_v24 hinv10 e_v24 s10
  step as ⟨e_v25, he_v25⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s11 _ _ rfl hinv11 h64 as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_v18 h_v22 h_v23 h_v24 dropping hinv11 s11
  replace h_v25 := Represents.rep_of_eq h_v25 (y := Eo.Term.String (SmtEval.native_string_lit "0")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v25]; decide)
  store_step with Store.apply_rep s12 v24 v25 _ _ hinv12 h64 h_v24 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_v18 h_v22 h_v23 dropping h_v24 h_v25 he_v25 hinv12 e_v25 s12 v24 v25
  step as ⟨e_v27, he_v27⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s13 _ _ rfl hinv13 h64 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_v18 h_v22 h_v23 h_v26 dropping hinv13 s13
  replace h_v27 := Represents.rep_of_eq h_v27 (y := Eo.Term.String (SmtEval.native_string_lit "9")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v27]; decide)
  store_step with Store.apply_rep s14 v26 v27 _ _ hinv14 h64 h_v26 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_v18 h_v22 h_v23 dropping h_v26 h_v27 he_v27 hinv14 e_v27 s14 v26 v27
  store_step with Store.apply_rep s15 v23 v28 _ _ hinv15 h64 h_v23 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_v18 h_v22 dropping h_v23 h_v28 hinv15 s15 v23 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s16 e_v30 (by rw [he_v30]; exact empty_args) hinv16 h64 as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_v18 h_v22 h_v29 dropping he_v30 hinv16 e_v30 s16
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s17 e_v31 (by rw [he_v31]; exact empty_args) hinv17 h64 as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 dropping he_v31 hinv17 e_v31 s17
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_re_2erange.construct s18 e_v32 (by rw [he_v32]; exact empty_args) hinv18 h64 as ⟨v32, s19, hinv19, h_v32⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 h_v31 dropping he_v32 hinv18 e_v32 s18
  step as ⟨e_v33, he_v33⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s19 _ _ rfl hinv19 h64 as ⟨v33, s20, hinv20, h_v33⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 h_v31 h_v32 dropping hinv19 s19
  replace h_v33 := Represents.rep_of_eq h_v33 (y := Eo.Term.String (SmtEval.native_string_lit "0")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v33]; decide)
  store_step with Store.apply_rep s20 v32 v33 _ _ hinv20 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s21, hinv21, h_v34⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 h_v31 dropping h_v32 h_v33 he_v33 hinv20 e_v33 s20 v32 v33
  step as ⟨e_v35, he_v35⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s21 _ _ rfl hinv21 h64 as ⟨v35, s22, hinv22, h_v35⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 h_v31 h_v34 dropping hinv21 s21
  replace h_v35 := Represents.rep_of_eq h_v35 (y := Eo.Term.String (SmtEval.native_string_lit "9")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v35]; decide)
  store_step with Store.apply_rep s22 v34 v35 _ _ hinv22 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s23, hinv23, h_v36⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 h_v31 dropping h_v34 h_v35 he_v35 hinv22 e_v35 s22 v34 v35
  store_step with Store.apply_rep s23 v31 v36 _ _ hinv23 h64 h_v31 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s24, hinv24, h_v37⟩ growing hG carrying h_v18 h_v22 h_v29 h_v30 dropping h_v31 h_v36 hinv23 s23 v31 v36
  store_step with Store.apply_rep s24 v30 v37 _ _ hinv24 h64 h_v30 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s25, hinv25, h_v38⟩ growing hG carrying h_v18 h_v22 h_v29 dropping h_v30 h_v37 hinv24 s24 v30 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s25 e_v39 (by rw [he_v39]; exact empty_args) hinv25 h64 as ⟨v39, s26, hinv26, h_v39⟩ growing hG carrying h_v18 h_v22 h_v29 h_v38 dropping he_v39 hinv25 e_v39 s25
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s26 _ _ rfl hinv26 h64 as ⟨v40, s27, hinv27, h_v40⟩ growing hG carrying h_v18 h_v22 h_v29 h_v38 h_v39 dropping hinv26 s26
  store_step with Store.apply_rep s27 v39 v40 _ _ hinv27 h64 h_v39 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s28, hinv28, h_v41⟩ growing hG carrying h_v18 h_v22 h_v29 h_v38 dropping h_v39 h_v40 hinv27 s27 v39 v40
  store_step with Store.apply_rep s28 v38 v41 _ _ hinv28 h64 h_v38 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s29, hinv29, h_v42⟩ growing hG carrying h_v18 h_v22 h_v29 dropping h_v38 h_v41 hinv28 s28 v38 v41
  store_step with Store.apply_rep s29 v29 v42 _ _ hinv29 h64 h_v29 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s30, hinv30, h_v43⟩ growing hG carrying h_v18 h_v22 dropping h_v29 h_v42 hinv29 s29 v29 v42
  store_step with Store.apply_rep s30 v22 v43 _ _ hinv30 h64 h_v22 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s31, hinv31, h_v44⟩ growing hG carrying h_v18 dropping h_v22 h_v43 hinv30 s30 v22 v43
  store_step with Store.apply_rep s31 v18 v44 _ _ hinv31 h64 h_v18 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s32, hinv32, h_v45⟩ growing hG carrying dropping h_v18 h_v44 hinv31 s31 v18 v44
  store_step with Store.literal_boolean_spec s32 true hinv32 h64 as ⟨v46, s33, hinv33, h_v46⟩ growing hG carrying h_v45 dropping hinv32 s32
  store_step with Store.apply_rep s33 v45 v46 _ _ hinv33 h64 h_v45 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s34, hinv34, h_v47⟩ growing hG carrying dropping h_v45 h_v46 hinv33 s33 v45 v46
  case_done hinv34 hG with h_v47 in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_in_re_from_int_nemp_dig_range` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_in_re_from_int_nemp_dig_range x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_in_re_from_int_nemp_dig_range
  unfold EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_from_int_nemp_dig_range x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_in_re_from_int_nemp_dig_range.case_0

theorem eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_in_re_from_int_nemp_dig_range x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2din_2dre_2dfrom_2dint_2dnemp_2ddig_2drange_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_in_re_inter_elim.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_in_re_inter_elim.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2einter.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_re_2einter.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v4 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a3 _ _ hinv7 h64 h_v6 h_a3 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v4 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v4 h_v7 hinv8 s8 v4 v7
  store_step with Store.apply_rep s9 v2 v8 _ _ hinv9 h64 h_v2 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v2 h_v8 hinv9 s9 v2 v8
  store_step with Store.apply_rep s10 v0 v9 _ _ hinv10 h64 h_v0 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v9 hinv10 s10 v0 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_and.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v10 dropping he_v11 hinv11 e_v11 s11
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v10 h_v11 dropping he_v12 hinv12 e_v12 s12
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v10 h_v11 dropping h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v13 a1 _ _ hinv14 h64 h_v13 h_a1 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a2 h_a3 h_v10 h_v11 dropping h_a1 h_v13 hinv14 s14 v13
  store_step with Store.apply_rep s15 v11 v14 _ _ hinv15 h64 h_v11 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a2 h_a3 h_v10 dropping h_v11 h_v14 hinv15 s15 v11 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_and.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a2 h_a3 h_v10 h_v15 dropping he_v16 hinv16 e_v16 s16
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a2 h_a3 h_v10 h_v15 h_v16 dropping he_v17 hinv17 e_v17 s17
  store_step with Store.apply_rep s18 v17 a0 _ _ hinv18 h64 h_v17 h_a0 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a2 h_a3 h_v10 h_v15 h_v16 dropping h_a0 h_v17 hinv18 s18 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_re_2einter.construct s19 e_v19 (by rw [he_v19]; exact empty_args) hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a2 h_a3 h_v10 h_v15 h_v16 h_v18 dropping he_v19 hinv19 e_v19 s19
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_re_2einter.construct s20 e_v20 (by rw [he_v20]; exact empty_args) hinv20 h64 as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a2 h_a3 h_v10 h_v15 h_v16 h_v18 h_v19 dropping he_v20 hinv20 e_v20 s20
  store_step with Store.apply_rep s21 v20 a2 _ _ hinv21 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a3 h_v10 h_v15 h_v16 h_v18 h_v19 dropping h_a2 h_v20 hinv21 s21 v20
  store_step with Store.apply_rep s22 v21 a3 _ _ hinv22 h64 h_v21 h_a3 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_v10 h_v15 h_v16 h_v18 h_v19 dropping h_a3 h_v21 hinv22 s22 v21
  step as ⟨e_v23, he_v23⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s23 e_v23 (by rw [he_v23]; rfl) h_v19 h_v22 hinv23 h64 (hG.rem hrem) op_not_left_eo_re_2einter op_nil_apply_eo_re_2einter as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_v10 h_v15 h_v16 h_v18 dropping h_v19 h_v22 he_v23 hinv23 e_v23 s23 v19 v22
  store_step with Store.apply_mk_rep s24 v18 v23 _ _ hinv24 h64 h_v18 h_v23 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_v10 h_v15 h_v16 dropping h_v18 h_v23 hinv24 s24 v18 v23
  store_step with Store.apply_mk_rep s25 v16 v24 _ _ hinv25 h64 h_v16 h_v24 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_v10 h_v15 dropping h_v16 h_v24 hinv25 s25 v16 v24
  store_step with Store.literal_boolean_spec s26 true hinv26 h64 as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_v10 h_v15 h_v25 dropping hinv26 s26
  store_step with Store.apply_mk_rep s27 v25 v26 _ _ hinv27 h64 h_v25 h_v26 as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_v10 h_v15 dropping h_v25 h_v26 hinv27 s27 v25 v26
  store_step with Store.apply_mk_rep s28 v15 v27 _ _ hinv28 h64 h_v15 h_v27 as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying h_v10 dropping h_v15 h_v27 hinv28 s28 v15 v27
  store_step with Store.apply_mk_rep s29 v10 v28 _ _ hinv29 h64 h_v10 h_v28 as ⟨v29, s30, hinv30, h_v29⟩ growing hG carrying dropping h_v10 h_v28 hinv29 s29 v10 v28
  case_done hinv30 hG with h_v29 in EoCases.__eo_prog_str_in_re_inter_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_str_in_re_inter_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_in_re_inter_elim x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_in_re_inter_elim.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_in_re_inter_elim
  unfold EoCases.__eo_prog_str_in_re_inter_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_in_re_inter_elim x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_in_re_inter_elim.case_0

theorem eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_in_re_inter_elim x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2din_2dre_2dinter_2delim_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
