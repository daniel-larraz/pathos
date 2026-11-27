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

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_lookahead_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_lookahead_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v4 hinv5 s5 v0 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ite.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 h_v5 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v5 h_v7 dropping hinv8 s8
  store_step with Store.apply_rep s9 v7 v8 _ _ hinv9 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v5 dropping h_v7 h_v8 hinv9 s9 v7 v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v5 dropping h_a1 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying dropping h_v10 h_v5 hinv11 s11 v10 v5
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_ite_then_lookahead_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_lookahead_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_lookahead_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_lookahead_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_lookahead_self
  unfold EoCases.__eo_prog_ite_then_lookahead_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_lookahead_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_lookahead_self.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_lookahead_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_not.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v3 v5 _ _ hinv6 h64 h_v3 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v2 dropping h_v3 h_v5 hinv6 s6 v3 v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a2 h_a3 h_v0 h_v2 dropping h_a1 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a2 h_a3 h_v0 h_v2 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v2 v8 _ _ hinv9 h64 h_v2 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a2 h_a3 h_v0 dropping h_v2 h_v8 hinv9 s9 v2 v8
  store_step with Store.apply_rep s10 v9 a3 _ _ hinv10 h64 h_v9 h_a3 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a2 h_a3 h_v0 dropping h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v0 v10 _ _ hinv11 h64 h_v0 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a2 h_a3 dropping h_v0 h_v10 hinv11 s11 v0 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a2 h_a3 h_v11 dropping he_v12 hinv12 e_v12 s12
  store_step with Store.apply_rep s13 v12 a0 _ _ hinv13 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a2 h_a3 h_v11 dropping h_a0 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v13 a2 _ _ hinv14 h64 h_v13 h_a2 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a3 h_v11 dropping h_a2 h_v13 hinv14 s14 v13
  store_step with Store.apply_rep s15 v14 a3 _ _ hinv15 h64 h_v14 h_a3 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v11 dropping h_a3 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v11 v15 _ _ hinv16 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v11 h_v15 hinv16 s16 v11 v15
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_ite_then_neg_lookahead.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_ite_then_neg_lookahead` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_neg_lookahead.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_neg_lookahead
  unfold EoCases.__eo_prog_ite_then_neg_lookahead.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_ite_then_neg_lookahead.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_neg_lookahead x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_then_true.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_then_true.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping hinv3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v6 dropping h_a0 h_v7 hinv8 s8 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v6 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v6 h_v8 dropping h_a1 h_v9 hinv10 s10 v9
  store_step with Store.literal_boolean_spec s11 false hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v6 h_v8 h_v10 dropping hinv11 s11
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v6 h_v8 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_rep s13 v8 v12 _ _ hinv13 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v6 dropping h_v12 h_v8 hinv13 s13 v12 v8
  store_step with Store.apply_rep s14 v6 v13 _ _ hinv14 h64 h_v6 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v6 hinv14 s14 v13 v6
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_ite_then_true.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_then_true` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dthen_2dtrue.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_then_true x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_then_true.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_then_true
  unfold EoCases.__eo_prog_ite_then_true.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dthen_2dtrue s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_then_true x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dthen_2dtrue.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dthen_2dtrue
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_then_true.case_0

theorem eo__24eo_5fprog_5fite_2dthen_2dtrue_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dthen_2dtrue.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dthen_2dtrue
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dthen_2dtrue s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_then_true x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dthen_2dtrue_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_true_cond.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_true_cond.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 dropping hinv2 s2
  store_step with Store.apply_rep s3 v1 v2 _ _ hinv3 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 h_v2 hinv3 s3 v1 v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 dropping h_a1 h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 dropping h_v0 h_v5 hinv6 s6 v0 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_a0 h_v6 hinv7 s7 v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_ite_true_cond.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_ite_true_cond` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_2dtrue_2dcond.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_ite_true_cond x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_true_cond.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_true_cond
  unfold EoCases.__eo_prog_ite_true_cond.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fite_2dtrue_2dcond s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_true_cond x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_2dtrue_2dcond.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fite_2dtrue_2dcond
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_ite_true_cond.case_0

theorem eo__24eo_5fprog_5fite_2dtrue_2dcond_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_2dtrue_2dcond.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fite_2dtrue_2dcond
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_2dtrue_2dcond s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_ite_true_cond x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_2dtrue_2dcond_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim1.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s e_v11 (by rw [he_v11]; exact empty_args) hinv h64 as ⟨v11, s1, hinv1, h_v11⟩ growing hG carrying h_v7 h_v9 h_v10 dropping h_a0 h_v1 h_v3 h_v4 h_v6 he_v11 e_v11 v1 v3 v4 v6
  pat_same v9 v11 with h_v9 h_v11 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v7 h_v10 dropping h_v11 h_v9 he_v12 hinv1 e_v12 s1 v11 v9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v7 h_v10 h_v12 dropping he_v13 hinv2 e_v13 s2
  store_step with Store.apply_rep s3 v13 v10 _ _ hinv3 h64 h_v13 h_v10 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v7 h_v12 dropping h_v10 h_v13 hinv3 s3 v10 v13
  store_step with Store.apply_rep s4 v12 v14 _ _ hinv4 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v7 dropping h_v12 h_v14 hinv4 s4 v12 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v7 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with Store.apply_rep s6 v16 v7 _ _ hinv6 h64 h_v16 h_v7 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v15 dropping h_v16 h_v7 hinv6 s6 v16 v7
  store_step with Store.literal_boolean_spec s7 false hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v15 h_v17 dropping hinv7 s7
  store_step with Store.apply_rep s8 v17 v18 _ _ hinv8 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v15 dropping h_v17 h_v18 hinv8 s8 v17 v18
  store_step with Store.apply_rep s9 v15 v19 _ _ hinv9 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying dropping h_v15 h_v19 hinv9 s9 v15 v19
  case_done hinv10 hG with h_v20 in EoCases.__eo_prog_ite_elim1.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v9 hn_v10

/-- logos's `__eo_prog_ite_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ite_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_ite_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_elim1
  unfold EoCases.__eo_prog_ite_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fite_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fite_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_ite_elim1.case_0

theorem eo__24eo_5fprog_5fite_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fite_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ite_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_elim2.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_ite.construct s e_v11 (by rw [he_v11]; exact empty_args) hinv h64 as ⟨v11, s1, hinv1, h_v11⟩ growing hG carrying h_v4 h_v9 h_v10 dropping h_a0 h_v1 h_v3 h_v6 h_v7 he_v11 e_v11 v1 v3 v6 v7
  pat_same v9 v11 with h_v9 h_v11 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_or.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v4 h_v10 dropping h_v11 h_v9 he_v12 hinv1 e_v12 s1 v11 v9
  store_step with Store.apply_rep s2 v12 v10 _ _ hinv2 h64 h_v12 h_v10 (by ns_tac) (by ns_tac) as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v4 dropping h_v10 h_v12 hinv2 s2 v10 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v4 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 v4 _ _ hinv4 h64 h_v14 h_v4 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v13 dropping h_v14 h_v4 hinv4 s4 v14 v4
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v13 h_v15 dropping hinv5 s5
  store_step with Store.apply_rep s6 v15 v16 _ _ hinv6 h64 h_v15 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v13 dropping h_v15 h_v16 hinv6 s6 v15 v16
  store_step with Store.apply_rep s7 v13 v17 _ _ hinv7 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying dropping h_v13 h_v17 hinv7 s7 v13 v17
  case_done hinv8 hG with h_v18 in EoCases.__eo_prog_ite_elim2.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v9 hn_v10

/-- logos's `__eo_prog_ite_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ite_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_ite_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_elim2
  unfold EoCases.__eo_prog_ite_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fite_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fite_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_ite_elim2.case_0

theorem eo__24eo_5fprog_5fite_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fite_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ite_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fite_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fite_5feq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ite_eq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ite_eq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fite_5feq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_eq.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_eq.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__eo_prog_ite_eq.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__eo_prog_ite_eq.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  store_step with Store.apply_rep s2 v10 v8 _ _ hinv2 h64 h_v10 h_v8 (by ns_tac) (by ns_tac) as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 hinv2 s2 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 dropping he_v12 hinv3 e_v12 s3
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_ite.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v12 dropping he_v13 hinv4 e_v13 s4
  store_step with Store.apply_rep s5 v13 v8 _ _ hinv5 h64 h_v13 h_v8 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v12 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_rep s6 v14 v5 _ _ hinv6 h64 h_v14 h_v5 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v12 dropping h_v14 hinv6 s6 v14
  store_step with Store.apply_rep s7 v15 v2 _ _ hinv7 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 h_v12 dropping h_v15 hinv7 s7 v15
  store_step with Store.apply_rep s8 v12 v16 _ _ hinv8 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 dropping h_v12 h_v16 hinv8 s8 v12 v16
  store_step with Store.apply_rep s9 v17 v5 _ _ hinv9 h64 h_v17 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v11 dropping h_v17 hinv9 s9 v17
  store_step with Store.apply_rep s10 v11 v18 _ _ hinv10 h64 h_v11 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v11 h_v18 hinv10 s10 v11 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v20 (by rw [he_v20]; exact empty_args) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v19 dropping he_v20 hinv11 e_v20 s11
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_ite.construct s12 e_v21 (by rw [he_v21]; exact empty_args) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v19 h_v20 dropping he_v21 hinv12 e_v21 s12
  store_step with Store.apply_rep s13 v21 v8 _ _ hinv13 h64 h_v21 h_v8 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v21 h_v8 hinv13 s13 v21 v8
  store_step with Store.apply_rep s14 v22 v5 _ _ hinv14 h64 h_v22 h_v5 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v19 h_v20 dropping h_v22 h_v5 hinv14 s14 v22 v5
  store_step with Store.apply_rep s15 v23 v2 _ _ hinv15 h64 h_v23 h_v2 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v19 h_v20 dropping h_v23 hinv15 s15 v23
  store_step with Store.apply_rep s16 v20 v24 _ _ hinv16 h64 h_v20 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v19 dropping h_v20 h_v24 hinv16 s16 v20 v24
  store_step with Store.apply_rep s17 v25 v2 _ _ hinv17 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v19 dropping h_v2 h_v25 hinv17 s17 v2 v25
  store_step with Store.apply_rep s18 v19 v26 _ _ hinv18 h64 h_v19 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying dropping h_v19 h_v26 hinv18 s18 v19 v26
  case_done hinv19 hG with h_v27 in EoCases.__eo_prog_ite_eq.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

/-- logos's `__eo_prog_ite_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fite_5feq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ite_eq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ite_eq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ite_eq
  unfold EoCases.__eo_prog_ite_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fite_5feq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fite_5feq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ite_eq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fite_5feq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fite_5feq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fite_5feq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_ite_eq.case_0

theorem eo__24eo_5fprog_5fite_5feq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fite_5feq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fite_5feq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fite_5feq s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ite_eq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fite_5feq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fmodus_5fponens_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fprog_5fmodus_5fponens s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_modus_ponens.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_modus_ponens.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fmodus_5fponens
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_unapply h_v3 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv else hinv hG in EoCases.__eo_prog_modus_ponens.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d_3e.construct s e_v10 (by rw [he_v10]; exact empty_args) hinv h64 as ⟨v10, s1, hinv1, h_v10⟩ growing hG carrying h_v1 h_v6 h_v8 h_v9 dropping h_a0 h_a1 h_v3 h_v5 he_v10 e_v10 v3 v5
  pat_same v8 v10 with h_v8 h_v10 using hinv1 else hinv1 hG in EoCases.__eo_prog_modus_ponens.case_0
  pat_same v9 v1 with h_v9 h_v1 using hinv1 else hinv1 hG in EoCases.__eo_prog_modus_ponens.case_0
  case_done hinv1 hG with h_v6 in EoCases.__eo_prog_modus_ponens.case_0 using hn_v5 hn_v6 hn_v8 hn_v9

/-- logos's `__eo_prog_modus_ponens` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fmodus_5fponens.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_modus_ponens x_a0 x_a1 =
      (firstSome [EoCases.__eo_prog_modus_ponens.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_modus_ponens
  unfold EoCases.__eo_prog_modus_ponens.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fmodus_5fponens_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fmodus_5fponens s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_modus_ponens x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fmodus_5fponens.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fmodus_5fponens
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fmodus_5fponens_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_modus_ponens.case_0

theorem eo__24eo_5fprog_5fmodus_5fponens_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fmodus_5fponens.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fmodus_5fponens
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fmodus_5fponens s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_modus_ponens x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fmodus_5fponens_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnary_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fnary_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_nary_cong.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_nary_cong.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnary_5fcong
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_nary_cong.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1 dropping h_a1 he_v2 e_v2
  store_step with Store.apply_rep s1 v2 a0 _ _ hinv1 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 dropping h_v2 hinv1 s1 v2
  store_step with ih.eo__24mk_5fnary_5fcong_5frhs s2 a0 v1 _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v1 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_v3 dropping h_a0 h_v1 hinv2 s2 v1
  store_step with Store.apply_mk_rep s3 v3 v4 _ _ hinv3 h64 h_v3 h_v4 as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying dropping h_v3 h_v4 hinv3 s3 v3 v4
  case_done hinv4 hG with h_v5 in EoCases.__eo_prog_nary_cong.case_0 using hn_a0

/-- logos's `__eo_prog_nary_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnary_5fcong.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_nary_cong x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_nary_cong.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_nary_cong
  unfold EoCases.__eo_prog_nary_cong.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnary_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fnary_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_nary_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnary_5fcong.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fnary_5fcong
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fnary_5fcong_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_nary_cong.case_0

theorem eo__24eo_5fprog_5fnary_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnary_5fcong.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fnary_5fcong
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnary_5fcong s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_nary_cong x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnary_5fcong_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_and.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_and.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fand
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_and.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_and.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_and.case_0
  store_step with ih.eo__24lower_5fnot_5fand s1 v4 _ hinv1 h64 (hG.rem hrem) h_v4 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying dropping h_v3 h_v4 h_v5 hinv1 s1 v3 v4 v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_prog_not_and.case_0 using hn_v3 hn_v4

/-- logos's `__eo_prog_not_and` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fand.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_and x_a0 =
      (firstSome [EoCases.__eo_prog_not_and.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_and
  unfold EoCases.__eo_prog_not_and.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_and x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fand.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fand
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fand_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_and.case_0

theorem eo__24eo_5fprog_5fnot_5fand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fand.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fand s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_and x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fand_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_equiv_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_equiv_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_equiv_elim1.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  store_step with Store.apply_rep s3 v13 v11 _ _ hinv3 h64 h_v13 h_v11 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v8 dropping h_v11 h_v13 hinv3 s3 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_or.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v8 h_v14 dropping he_v15 hinv4 e_v15 s4
  store_step with Store.apply_rep s5 v15 v8 _ _ hinv5 h64 h_v15 h_v8 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v14 dropping h_v15 h_v8 hinv5 s5 v15 v8
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v14 h_v16 dropping hinv6 s6
  store_step with Store.apply_rep s7 v16 v17 _ _ hinv7 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v14 dropping h_v16 h_v17 hinv7 s7 v16 v17
  store_step with Store.apply_rep s8 v14 v18 _ _ hinv8 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying dropping h_v14 h_v18 hinv8 s8 v14 v18
  case_done hinv9 hG with h_v19 in EoCases.__eo_prog_not_equiv_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_equiv_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fequiv_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_equiv_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_equiv_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_equiv_elim1
  unfold EoCases.__eo_prog_not_equiv_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fequiv_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_equiv_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fequiv_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fequiv_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_equiv_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fequiv_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fequiv_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fequiv_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_equiv_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fequiv_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_equiv_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_equiv_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_equiv_elim2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v8 h_v11 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 v11 _ _ hinv4 h64 h_v14 h_v11 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v8 h_v13 dropping h_v11 h_v14 hinv4 s4 v11 v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v8 dropping h_v13 h_v15 hinv5 s5 v13 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_or.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v8 h_v16 dropping he_v17 hinv6 e_v17 s6
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_not.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v8 h_v16 h_v17 dropping he_v18 hinv7 e_v18 s7
  store_step with Store.apply_rep s8 v18 v8 _ _ hinv8 h64 h_v18 h_v8 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v16 h_v17 dropping h_v18 h_v8 hinv8 s8 v18 v8
  store_step with Store.apply_rep s9 v17 v19 _ _ hinv9 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v16 dropping h_v17 h_v19 hinv9 s9 v17 v19
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_v16 h_v20 dropping hinv10 s10
  store_step with Store.apply_rep s11 v20 v21 _ _ hinv11 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_v16 dropping h_v20 h_v21 hinv11 s11 v20 v21
  store_step with Store.apply_rep s12 v16 v22 _ _ hinv12 h64 h_v16 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying dropping h_v16 h_v22 hinv12 s12 v16 v22
  case_done hinv13 hG with h_v23 in EoCases.__eo_prog_not_equiv_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_equiv_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fequiv_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_equiv_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_equiv_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_equiv_elim2
  unfold EoCases.__eo_prog_not_equiv_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fequiv_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_equiv_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fequiv_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fequiv_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_equiv_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fequiv_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fequiv_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fequiv_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_equiv_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fequiv_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_implies_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_implies_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_implies_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_implies_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d_3e.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_implies_elim1.case_0
  case_done hinv2 hG with h_v11 in EoCases.__eo_prog_not_implies_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_implies_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fimplies_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_implies_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_implies_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_implies_elim1
  unfold EoCases.__eo_prog_not_implies_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fimplies_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_implies_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fimplies_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fimplies_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_implies_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fimplies_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fimplies_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fimplies_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_implies_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fimplies_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_implies_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_implies_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_implies_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_implies_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d_3e.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 dropping h_v11 h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v11 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_implies_elim2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_not.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  store_step with Store.apply_rep s3 v13 v8 _ _ hinv3 h64 h_v13 h_v8 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying dropping h_v13 h_v8 hinv3 s3 v13 v8
  case_done hinv4 hG with h_v14 in EoCases.__eo_prog_not_implies_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_implies_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fimplies_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_implies_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_implies_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_implies_elim2
  unfold EoCases.__eo_prog_not_implies_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fimplies_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_implies_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fimplies_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fimplies_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_implies_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fimplies_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fimplies_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fimplies_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_implies_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fimplies_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_ite_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_ite_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fite_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_ite_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_v11 h_v13 h_v14 dropping h_v10 h_v3 h_v4 h_v5 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v3 v4 v5 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_ite_elim1.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_v11 h_v14 dropping h_v13 h_v15 he_v16 hinv2 e_v16 s2 v13 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_not.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_v11 h_v14 h_v16 dropping he_v17 hinv3 e_v17 s3
  store_step with Store.apply_rep s4 v17 v14 _ _ hinv4 h64 h_v17 h_v14 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_v11 h_v16 dropping h_v14 h_v17 hinv4 s4 v14 v17
  store_step with Store.apply_rep s5 v16 v18 _ _ hinv5 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_v11 dropping h_v16 h_v18 hinv5 s5 v16 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v11 h_v19 dropping he_v20 hinv6 e_v20 s6
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_not.construct s7 e_v21 (by rw [he_v21]; exact empty_args) hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_v11 h_v19 h_v20 dropping he_v21 hinv7 e_v21 s7
  store_step with Store.apply_rep s8 v21 v11 _ _ hinv8 h64 h_v21 h_v11 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_v19 h_v20 dropping h_v11 h_v21 hinv8 s8 v11 v21
  store_step with Store.apply_rep s9 v20 v22 _ _ hinv9 h64 h_v20 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_v19 dropping h_v20 h_v22 hinv9 s9 v20 v22
  store_step with Store.literal_boolean_spec s10 false hinv10 h64 as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_v19 h_v23 dropping hinv10 s10
  store_step with Store.apply_rep s11 v23 v24 _ _ hinv11 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_v19 dropping h_v23 h_v24 hinv11 s11 v23 v24
  store_step with Store.apply_rep s12 v19 v25 _ _ hinv12 h64 h_v19 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying dropping h_v19 h_v25 hinv12 s12 v19 v25
  case_done hinv13 hG with h_v26 in EoCases.__eo_prog_not_ite_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_not_ite_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fite_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_ite_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_ite_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_ite_elim1
  unfold EoCases.__eo_prog_not_ite_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fite_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fite_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_ite_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fite_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fite_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fite_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_ite_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fite_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fite_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fite_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fite_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_ite_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fite_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_ite_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_ite_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fite_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_ite_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_v8 h_v13 h_v14 dropping h_v10 h_v11 h_v3 h_v4 h_v5 h_v7 he_v15 hinv1 e_v15 s1 v10 v11 v3 v4 v5 v7
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_ite_elim2.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_or.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_v8 h_v14 dropping h_v13 h_v15 he_v16 hinv2 e_v16 s2 v13 v15
  store_step with Store.apply_rep s3 v16 v14 _ _ hinv3 h64 h_v16 h_v14 (by ns_tac) (by ns_tac) as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_v8 dropping h_v14 h_v16 hinv3 s3 v14 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_v8 h_v17 dropping he_v18 hinv4 e_v18 s4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_not.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_v8 h_v17 h_v18 dropping he_v19 hinv5 e_v19 s5
  store_step with Store.apply_rep s6 v19 v8 _ _ hinv6 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_v17 h_v18 dropping h_v19 h_v8 hinv6 s6 v19 v8
  store_step with Store.apply_rep s7 v18 v20 _ _ hinv7 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_v17 dropping h_v18 h_v20 hinv7 s7 v18 v20
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_v17 h_v21 dropping hinv8 s8
  store_step with Store.apply_rep s9 v21 v22 _ _ hinv9 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_v17 dropping h_v21 h_v22 hinv9 s9 v21 v22
  store_step with Store.apply_rep s10 v17 v23 _ _ hinv10 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying dropping h_v17 h_v23 hinv10 s10 v17 v23
  case_done hinv11 hG with h_v24 in EoCases.__eo_prog_not_ite_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_not_ite_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fite_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_ite_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_ite_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_ite_elim2
  unfold EoCases.__eo_prog_not_ite_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fite_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fite_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_ite_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fite_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fite_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fite_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_ite_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fite_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fite_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fite_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fite_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_ite_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fite_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fnot_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fnot_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_not_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_not_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fnot_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_not_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_not_elim.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_not_elim.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_not_elim.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_not.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_v7 h_v8 dropping h_v3 h_v4 h_v5 he_v9 hinv1 e_v9 s1 v3 v4 v5
  pat_same v7 v9 with h_v7 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_not_elim.case_0
  case_done hinv2 hG with h_v8 in EoCases.__eo_prog_not_not_elim.case_0 using hn_v3 hn_v4 hn_v7 hn_v8

/-- logos's `__eo_prog_not_not_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fnot_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_not_elim x_a0 =
      (firstSome [EoCases.__eo_prog_not_not_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_not_elim
  unfold EoCases.__eo_prog_not_not_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fnot_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fnot_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_not_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fnot_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fnot_5felim
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fnot_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_not_elim.case_0

theorem eo__24eo_5fprog_5fnot_5fnot_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fnot_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fnot_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fnot_5felim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_not_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fnot_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5for_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fnot_5for_5felim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_or_elim.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_or_elim.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5for_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_or_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_or_elim.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v3 h_v4 dropping h_a1 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_or_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_not.construct s1 e_v6 (by rw [he_v6]; exact empty_args) hinv1 h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_v3 h_v5 he_v6 hinv1 e_v6 s1 v3 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_or.construct s2 e_v7 (by rw [he_v7]; exact empty_args) hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_v4 h_v6 dropping he_v7 hinv2 e_v7 s2
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_list_nth n ih.eo__24eo_5fis_5flist_5fnil s3 e_v8 (by rw [he_v8]; rfl) h_v7 h_v4 h_a0 hinv3 h64 (hG.rem hrem) op_not_left_eo_or as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_v6 dropping h_a0 h_v4 h_v7 he_v8 hinv3 e_v8 s3 v4 v7
  store_step with Store.apply_mk_rep s4 v6 v8 _ _ hinv4 h64 h_v6 h_v8 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying dropping h_v6 h_v8 hinv4 s4 v6 v8
  case_done hinv5 hG with h_v9 in EoCases.__eo_prog_not_or_elim.case_0 using hn_a0 hn_v3 hn_v4

/-- logos's `__eo_prog_not_or_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5for_5felim.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_not_or_elim x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_not_or_elim.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_or_elim
  unfold EoCases.__eo_prog_not_or_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5for_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fnot_5for_5felim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_or_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5for_5felim.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fnot_5for_5felim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fnot_5for_5felim_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_not_or_elim.case_0

theorem eo__24eo_5fprog_5fnot_5for_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5for_5felim.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fnot_5for_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5for_5felim s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_not_or_elim x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5for_5felim_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_xor_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_xor_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_xor_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_xor_elim1.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_xor_elim1.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  store_step with Store.apply_rep s3 v13 v11 _ _ hinv3 h64 h_v13 h_v11 (by ns_tac) (by ns_tac) as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v8 dropping h_v11 h_v13 hinv3 s3 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_or.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v8 h_v14 dropping he_v15 hinv4 e_v15 s4
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_not.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v8 h_v14 h_v15 dropping he_v16 hinv5 e_v16 s5
  store_step with Store.apply_rep s6 v16 v8 _ _ hinv6 h64 h_v16 h_v8 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v14 h_v15 dropping h_v16 h_v8 hinv6 s6 v16 v8
  store_step with Store.apply_rep s7 v15 v17 _ _ hinv7 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v14 dropping h_v15 h_v17 hinv7 s7 v15 v17
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v14 h_v18 dropping hinv8 s8
  store_step with Store.apply_rep s9 v18 v19 _ _ hinv9 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v14 dropping h_v18 h_v19 hinv9 s9 v18 v19
  store_step with Store.apply_rep s10 v14 v20 _ _ hinv10 h64 h_v14 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying dropping h_v14 h_v20 hinv10 s10 v14 v20
  case_done hinv11 hG with h_v21 in EoCases.__eo_prog_not_xor_elim1.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_xor_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fxor_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_xor_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_not_xor_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_xor_elim1
  unfold EoCases.__eo_prog_not_xor_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_xor_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fxor_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fxor_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_xor_elim1.case_0

theorem eo__24eo_5fprog_5fnot_5fxor_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fxor_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fxor_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fxor_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_xor_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fxor_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_not_xor_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_not_xor_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_not_xor_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_not_xor_elim2.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v3 h_v4 dropping h_a0 h_v1 he_v5 e_v5 v1
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_v8 h_v10 h_v11 dropping h_v3 h_v4 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v3 v4 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_not_xor_elim2.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_v8 h_v11 dropping h_v10 h_v12 he_v13 hinv2 e_v13 s2 v10 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_v8 h_v11 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 v11 _ _ hinv4 h64 h_v14 h_v11 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_v8 h_v13 dropping h_v11 h_v14 hinv4 s4 v11 v14
  store_step with Store.apply_rep s5 v13 v15 _ _ hinv5 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_v8 dropping h_v13 h_v15 hinv5 s5 v13 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_or.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_v8 h_v16 dropping he_v17 hinv6 e_v17 s6
  store_step with Store.apply_rep s7 v17 v8 _ _ hinv7 h64 h_v17 h_v8 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_v16 dropping h_v17 h_v8 hinv7 s7 v17 v8
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_v16 h_v18 dropping hinv8 s8
  store_step with Store.apply_rep s9 v18 v19 _ _ hinv9 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_v16 dropping h_v18 h_v19 hinv9 s9 v18 v19
  store_step with Store.apply_rep s10 v16 v20 _ _ hinv10 h64 h_v16 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying dropping h_v16 h_v20 hinv10 s10 v16 v20
  case_done hinv11 hG with h_v21 in EoCases.__eo_prog_not_xor_elim2.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_not_xor_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fnot_5fxor_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_not_xor_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_not_xor_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_not_xor_elim2
  unfold EoCases.__eo_prog_not_xor_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fnot_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_not_xor_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fnot_5fxor_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fnot_5fxor_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_not_xor_elim2.case_0

theorem eo__24eo_5fprog_5fnot_5fxor_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fnot_5fxor_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fnot_5fxor_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fnot_5fxor_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_not_xor_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fnot_5fxor_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fpairwise_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fpairwise_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_pairwise_cong.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_pairwise_cong.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fpairwise_5fcong
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_pairwise_cong.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_prog_pairwise_cong.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_v1 h_v2 h_v4 dropping h_a0 h_a1 he_v5 e_v5
  store_step with Store.apply_rep s1 v1 v2 _ _ hinv1 h64 h_v1 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v1 h_v2 h_v4 h_v5 dropping hinv1 s1
  store_step with Store.apply_rep s2 v5 v6 _ _ hinv2 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_v1 h_v2 h_v4 dropping h_v5 h_v6 hinv2 s2 v5 v6
  store_step with ih.eo__24mk_5fnary_5fcong_5frhs s3 v2 v4 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v4 as ⟨v8, s4, hinv4, h_v8⟩ growing hG carrying h_v1 h_v7 dropping h_v2 h_v4 hinv3 s3 v2 v4
  store_step with Store.apply_mk_rep s4 v1 v8 _ _ hinv4 h64 h_v1 h_v8 as ⟨v9, s5, hinv5, h_v9⟩ growing hG carrying h_v7 dropping h_v1 h_v8 hinv4 s4 v1 v8
  store_step with Store.apply_mk_rep s5 v7 v9 _ _ hinv5 h64 h_v7 h_v9 as ⟨v10, s6, hinv6, h_v10⟩ growing hG carrying dropping h_v7 h_v9 hinv5 s5 v7 v9
  case_done hinv6 hG with h_v10 in EoCases.__eo_prog_pairwise_cong.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_prog_pairwise_cong` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fpairwise_5fcong.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_pairwise_cong x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_pairwise_cong.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_pairwise_cong
  unfold EoCases.__eo_prog_pairwise_cong.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fpairwise_5fcong_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fpairwise_5fcong s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_pairwise_cong x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fpairwise_5fcong.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fpairwise_5fcong
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fpairwise_5fcong_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_pairwise_cong.case_0

theorem eo__24eo_5fprog_5fpairwise_5fcong_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fpairwise_5fcong.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fpairwise_5fcong
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fpairwise_5fcong s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_pairwise_cong x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fpairwise_5fcong_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_process_scope.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_process_scope.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fprocess_5fscope
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_process_scope.case_0
  store_step with ih.eo__24run_5fprocess_5fscope s v1 a0 _ _ hinv h64 hrem h_v1 h_a0 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying dropping h_a0 h_a1 h_v1 v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_prog_process_scope.case_0 using hn_a0

/-- logos's `__eo_prog_process_scope` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fprocess_5fscope.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_process_scope x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_process_scope.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_process_scope
  unfold EoCases.__eo_prog_process_scope.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fprocess_5fscope_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fprocess_5fscope s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_process_scope x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fprocess_5fscope.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fprocess_5fscope
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fprocess_5fscope_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_process_scope.case_0

theorem eo__24eo_5fprog_5fprocess_5fscope_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fprocess_5fscope.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fprocess_5fscope
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fprocess_5fscope s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_process_scope x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fprocess_5fscope_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_dt_split.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_dt_split.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_dt_split.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_dt_split.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_dt_split.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_dt_split.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_dt_split.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_dt_split.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_dt_split.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_dt_split.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_v2 h_v9 h_v16 h_v18 h_v19 dropping h_v11 h_v12 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v12 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_dt_split.case_0
  store_step with ih.eo__24eo_5ftypeof s3 v19 _ hinv3 h64 (hG.rem hrem) h_v19 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 dropping h_v18 h_v20 hinv3 s3 v18 v20
  store_step with ih.eo__24dt_5fget_5fconstructors s4 v21 _ hinv4 h64 (hG.rem hrem) h_v21 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 dropping h_v21 hinv4 s4 v21
  store_step with ih.eo__24is_5fquant_5fdt_5fsplit s5 v19 v22 v16 v9 v2 _ _ _ _ _ hinv5 h64 (hG.rem hrem) h_v19 h_v22 h_v16 h_v9 h_v2 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 dropping h_v22 hinv5 s5 v22
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 h_v23 dropping hinv6 s6
  have h_req_v34 := (show requires_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit s7 v23 v24 v19 v16 v9 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v23 v24 with h_v23 h_v24 using hinv7 hG
    req_stuck h_v23 as hq_v23 using hinv7 hG
    step as ⟨e_v25, he_v25⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v25 (by rw [he_v25]; exact empty_args) hinv7 h64 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 dropping h_v23 h_v24 he_v25 hinv7 e_v25 s7 v23 v24
    step as ⟨e_v26, he_v26⟩
    store_step with CtorSpec.eo_forall.construct s8 e_v26 (by rw [he_v26]; exact empty_args) hinv8 h64 as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 h_v25 dropping he_v26 hinv8 e_v26 s8
    step as ⟨e_v27, he_v27⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s9 e_v27 (by rw [he_v27]; exact empty_args) hinv9 h64 as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 h_v25 h_v26 dropping he_v27 hinv9 e_v27 s9
    store_step with Store.apply_rep s10 v27 v19 _ _ hinv10 h64 h_v27 h_v19 (by ns_tac) (by ns_tac) as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying h_v2 h_v9 h_v16 h_v25 h_v26 dropping h_v19 h_v27 hinv10 s10 v19 v27
    store_step with Store.apply_rep s11 v28 v16 _ _ hinv11 h64 h_v28 h_v16 (by ns_tac) (by ns_tac) as ⟨v29, s12, hinv12, h_v29⟩ growing hG carrying h_v2 h_v9 h_v25 h_v26 dropping h_v16 h_v28 hinv11 s11 v16 v28
    store_step with Store.apply_rep s12 v26 v29 _ _ hinv12 h64 h_v26 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s13, hinv13, h_v30⟩ growing hG carrying h_v2 h_v9 h_v25 dropping h_v26 h_v29 hinv12 s12 v26 v29
    store_step with Store.apply_rep s13 v30 v9 _ _ hinv13 h64 h_v30 h_v9 (by ns_tac) (by ns_tac) as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying h_v2 h_v25 dropping h_v30 h_v9 hinv13 s13 v30 v9
    store_step with Store.apply_rep s14 v25 v31 _ _ hinv14 h64 h_v25 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s15, hinv15, h_v32⟩ growing hG carrying h_v2 dropping h_v25 h_v31 hinv14 s14 v25 v31
    store_step with Store.apply_rep s15 v32 v2 _ _ hinv15 h64 h_v32 h_v2 (by ns_tac) (by ns_tac) as ⟨v33, s16, hinv16, h_v33⟩ growing hG carrying dropping h_v2 h_v32 hinv15 s15 v2 v32
    req_done hinv16 hG with h_v33 using hq_v23)
  store_step with h_req_v34 as ⟨v34, s17, hinv17, h_v34⟩ growing hG carrying dropping h_req_v34 h_v16 h_v19 h_v2 h_v23 h_v24 h_v9 hinv7 s7 v16 v19 v2 v23 v24 v9
  case_done hinv17 hG with h_v34 in EoCases.__eo_prog_quant_dt_split.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

/-- logos's `__eo_prog_quant_dt_split` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2ddt_2dsplit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_dt_split x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_dt_split.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_dt_split
  unfold EoCases.__eo_prog_quant_dt_split.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2ddt_2dsplit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2ddt_2dsplit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_dt_split x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2ddt_2dsplit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2ddt_2dsplit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_dt_split.case_0

theorem eo__24eo_5fprog_5fquant_2ddt_2dsplit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2ddt_2dsplit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2ddt_2dsplit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2ddt_2dsplit s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_dt_split x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2ddt_2dsplit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_merge_prenex.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_merge_prenex.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_merge_prenex.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_merge_prenex.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_merge_prenex.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_merge_prenex.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_merge_prenex.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_eq s2 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v13 he_v14 hinv2 e_v14 s2 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_exists.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v14 dropping he_v15 hinv3 e_v15 s3
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_eq s4 e_v16 (by rw [he_v16]; rfl) h_v11 h_v15 hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v14 dropping h_v15 he_v16 hinv4 e_v16 s4 v15
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_or s5 e_v17 (by rw [he_v17]; rfl) h_v14 h_v16 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v14 h_v16 he_v17 hinv5 e_v17 s5 v14 v16
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v17 dropping hinv6 s6
  have h_req_v29 := (show requires_1_eo__24eo_5fprog_5fquant_2dmerge_2dprenex s7 v17 v18 v11 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fquant_2dmerge_2dprenex
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v17 v18 with h_v17 h_v18 using hinv7 hG
    req_stuck h_v17 as hq_v17 using hinv7 hG
    store_step with Store.apply_rep s7 v11 v12 _ _ hinv7 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v17 h_v18 hinv7 s7 v17 v18
    store_step with Store.apply_rep s8 v19 v9 _ _ hinv8 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v19 hinv8 s8 v19
    step as ⟨e_v21, he_v21⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s9 e_v21 (by rw [he_v21]; exact empty_args) hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v20 dropping he_v21 hinv9 e_v21 s9
    store_step with ih.eo__24mk_5fquant_5fmerge_5fprenex s10 v11 v20 v21 _ _ _ hinv10 h64 (hG.rem hrem) h_v11 h_v20 h_v21 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v20 h_v21 hinv10 s10 v20 v21
    have h_req_v28 := (show requires_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex s11 v22 v2 v11 v12 v9 ⦃ r s' => s'.Inv ∧ s11.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s11
      req_same v22 v2 with h_v22 h_v2 using hinv11 hG
      req_stuck h_v22 as hq_v22 using hinv11 hG
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo__3d.construct s11 e_v23 (by rw [he_v23]; exact empty_args) hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v22 he_v23 hinv11 e_v23 s11 v22
      store_step with Store.apply_rep s12 v11 v12 _ _ hinv12 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v2 h_v9 h_v23 dropping h_v11 h_v12 hinv12 s12 v11 v12
      store_step with Store.apply_rep s13 v24 v9 _ _ hinv13 h64 h_v24 h_v9 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v2 h_v23 dropping h_v24 h_v9 hinv13 s13 v24 v9
      store_step with Store.apply_rep s14 v23 v25 _ _ hinv14 h64 h_v23 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v2 dropping h_v23 h_v25 hinv14 s14 v23 v25
      store_step with Store.apply_rep s15 v26 v2 _ _ hinv15 h64 h_v26 h_v2 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying dropping h_v2 h_v26 hinv15 s15 v2 v26
      req_done hinv16 hG with h_v27 using hq_v22)
    store_step with h_req_v28 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying dropping h_req_v28 h_v11 h_v12 h_v2 h_v22 h_v9 hinv11 s11 v11 v12 v2 v22 v9
    req_done hinv17 hG with h_v28 using hq_v17)
  store_step with h_req_v29 as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying dropping h_req_v29 h_v11 h_v12 h_v17 h_v18 h_v2 h_v9 hinv7 s7 v11 v12 v17 v18 v2 v9
  case_done hinv18 hG with h_v29 in EoCases.__eo_prog_quant_merge_prenex.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_quant_merge_prenex` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2dmerge_2dprenex.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_merge_prenex x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_merge_prenex.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_merge_prenex
  unfold EoCases.__eo_prog_quant_merge_prenex.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_merge_prenex x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2dmerge_2dprenex.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_merge_prenex.case_0

theorem eo__24eo_5fprog_5fquant_2dmerge_2dprenex_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2dmerge_2dprenex.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2dmerge_2dprenex
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_merge_prenex x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_miniscope_and.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_miniscope_and.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_miniscope_and.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_miniscope_and.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_and.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_and.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_and.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_miniscope_and.case_0
  store_step with ih.eo__24mk_5fquant_5fminiscope_5fand s2 v12 v9 _ _ hinv2 h64 (hG.rem hrem) h_v12 h_v9 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  have h_req_v21 := (show requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand s3 v14 v2 v12 v9 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v14 v2 with h_v14 h_v2 using hinv3 hG
    req_stuck h_v14 as hq_v14 using hinv3 hG
    step as ⟨e_v15, he_v15⟩
    store_step with CtorSpec.eo__3d.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 he_v15 hinv3 e_v15 s3 v14
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo_forall.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 h_v15 dropping he_v16 hinv4 e_v16 s4
    store_step with Store.apply_rep s5 v16 v12 _ _ hinv5 h64 h_v16 h_v12 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v15 dropping h_v12 h_v16 hinv5 s5 v12 v16
    store_step with Store.apply_rep s6 v17 v9 _ _ hinv6 h64 h_v17 h_v9 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v15 dropping h_v17 h_v9 hinv6 s6 v17 v9
    store_step with Store.apply_rep s7 v15 v18 _ _ hinv7 h64 h_v15 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 dropping h_v15 h_v18 hinv7 s7 v15 v18
    store_step with Store.apply_rep s8 v19 v2 _ _ hinv8 h64 h_v19 h_v2 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying dropping h_v19 h_v2 hinv8 s8 v19 v2
    req_done hinv9 hG with h_v20 using hq_v14)
  store_step with h_req_v21 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_req_v21 h_v12 h_v14 h_v2 h_v9 hinv3 s3 v12 v14 v2 v9
  case_done hinv10 hG with h_v21 in EoCases.__eo_prog_quant_miniscope_and.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_quant_miniscope_and` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2dminiscope_2dand.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_miniscope_and x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_miniscope_and.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_miniscope_and
  unfold EoCases.__eo_prog_quant_miniscope_and.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2dminiscope_2dand_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2dminiscope_2dand s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_miniscope_and x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2dminiscope_2dand.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2dminiscope_2dand
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_miniscope_and.case_0

theorem eo__24eo_5fprog_5fquant_2dminiscope_2dand_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2dminiscope_2dand.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2dminiscope_2dand
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2dminiscope_2dand s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_miniscope_and x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2dminiscope_2dand_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_miniscope_ite.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_miniscope_ite.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v9 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v18 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v23 (by rw [he_v23]; exact empty_args) hinv2 h64 as ⟨v23, s3, hinv3, h_v23⟩ growing hG carrying h_v2 h_v12 h_v16 h_v19 h_v21 h_v22 dropping h_v11 h_v13 h_v15 h_v18 h_v9 he_v23 hinv2 e_v23 s2 v11 v13 v15 v18 v9
  pat_same v21 v23 with h_v21 h_v23 using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v2 as ⟨v25, v26, x_v25, x_v26, h_v25, h_v26, hn_v25, hn_v26⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v33 (by rw [he_v33]; exact empty_args) hinv3 h64 as ⟨v33, s4, hinv4, h_v33⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v26 h_v29 h_v31 h_v32 dropping h_v2 h_v21 h_v23 h_v25 h_v28 he_v33 hinv3 e_v33 s3 v2 v21 v23 v25 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv4 else hinv4 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_same v32 v22 with h_v32 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v29 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_forall.construct s4 e_v40 (by rw [he_v40]; exact empty_args) hinv4 h64 as ⟨v40, s5, hinv5, h_v40⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v26 h_v36 h_v38 h_v39 dropping h_v29 h_v31 h_v32 h_v33 h_v35 he_v40 hinv4 e_v40 s4 v29 v31 v32 v33 v35
  pat_same v38 v40 with h_v38 h_v40 using hinv5 else hinv5 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_same v39 v12 with h_v39 h_v12 using hinv5 else hinv5 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_same v36 v19 with h_v36 h_v19 using hinv5 else hinv5 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v26 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_forall.construct s5 e_v47 (by rw [he_v47]; exact empty_args) hinv5 h64 as ⟨v47, s6, hinv6, h_v47⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v43 h_v45 h_v46 dropping h_v26 h_v36 h_v38 h_v39 h_v40 h_v42 he_v47 hinv5 e_v47 s5 v26 v36 v38 v39 v40 v42
  pat_same v45 v47 with h_v45 h_v47 using hinv6 else hinv6 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_same v46 v12 with h_v46 h_v12 using hinv6 else hinv6 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  pat_same v43 v16 with h_v43 h_v16 using hinv6 else hinv6 hG in EoCases.__eo_prog_quant_miniscope_ite.case_0
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s6 e_v48 (by rw [he_v48]; exact empty_args) hinv6 h64 as ⟨v48, s7, hinv7, h_v48⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 dropping h_v43 h_v45 h_v46 h_v47 he_v48 hinv6 e_v48 s6 v43 v45 v46 v47
  store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s7 v22 v12 v48 _ _ _ hinv7 h64 (hG.rem hrem) h_v22 h_v12 h_v48 as ⟨v49, s8, hinv8, h_v49⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 dropping h_v48 hinv7 s7 v48
  store_step with Store.literal_boolean_spec s8 false hinv8 h64 as ⟨v50, s9, hinv9, h_v50⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v49 dropping hinv8 s8
  have h_req_v71 := (show requires_1_eo__24eo_5fprog_5fquant_2dminiscope_2dite s9 v49 v50 v12 v22 v19 v16 ⦃ r s' => s'.Inv ∧ s9.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fquant_2dminiscope_2dite
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s9
    req_same v49 v50 with h_v49 h_v50 using hinv9 hG
    req_stuck h_v49 as hq_v49 using hinv9 hG
    step as ⟨e_v51, he_v51⟩
    store_step with CtorSpec.eo__3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 dropping h_v49 h_v50 he_v51 hinv9 e_v51 s9 v49 v50
    step as ⟨e_v52, he_v52⟩
    store_step with CtorSpec.eo_forall.construct s10 e_v52 (by rw [he_v52]; exact empty_args) hinv10 h64 as ⟨v52, s11, hinv11, h_v52⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 dropping he_v52 hinv10 e_v52 s10
    store_step with Store.apply_rep s11 v52 v12 _ _ hinv11 h64 h_v52 h_v12 (by ns_tac) (by ns_tac) as ⟨v53, s12, hinv12, h_v53⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 dropping h_v52 hinv11 s11 v52
    step as ⟨e_v54, he_v54⟩
    store_step with CtorSpec.eo_ite.construct s12 e_v54 (by rw [he_v54]; exact empty_args) hinv12 h64 as ⟨v54, s13, hinv13, h_v54⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 h_v53 dropping he_v54 hinv12 e_v54 s12
    store_step with Store.apply_rep s13 v54 v22 _ _ hinv13 h64 h_v54 h_v22 (by ns_tac) (by ns_tac) as ⟨v55, s14, hinv14, h_v55⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 h_v53 dropping h_v54 hinv13 s13 v54
    store_step with Store.apply_rep s14 v55 v19 _ _ hinv14 h64 h_v55 h_v19 (by ns_tac) (by ns_tac) as ⟨v56, s15, hinv15, h_v56⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 h_v53 dropping h_v55 hinv14 s14 v55
    store_step with Store.apply_rep s15 v56 v16 _ _ hinv15 h64 h_v56 h_v16 (by ns_tac) (by ns_tac) as ⟨v57, s16, hinv16, h_v57⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 h_v53 dropping h_v56 hinv15 s15 v56
    store_step with Store.apply_rep s16 v53 v57 _ _ hinv16 h64 h_v53 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s17, hinv17, h_v58⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v51 dropping h_v53 h_v57 hinv16 s16 v53 v57
    store_step with Store.apply_rep s17 v51 v58 _ _ hinv17 h64 h_v51 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s18, hinv18, h_v59⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 dropping h_v51 h_v58 hinv17 s17 v51 v58
    step as ⟨e_v60, he_v60⟩
    store_step with CtorSpec.eo_ite.construct s18 e_v60 (by rw [he_v60]; exact empty_args) hinv18 h64 as ⟨v60, s19, hinv19, h_v60⟩ growing hG carrying h_v12 h_v16 h_v19 h_v22 h_v59 dropping he_v60 hinv18 e_v60 s18
    store_step with Store.apply_rep s19 v60 v22 _ _ hinv19 h64 h_v60 h_v22 (by ns_tac) (by ns_tac) as ⟨v61, s20, hinv20, h_v61⟩ growing hG carrying h_v12 h_v16 h_v19 h_v59 dropping h_v22 h_v60 hinv19 s19 v22 v60
    step as ⟨e_v62, he_v62⟩
    store_step with CtorSpec.eo_forall.construct s20 e_v62 (by rw [he_v62]; exact empty_args) hinv20 h64 as ⟨v62, s21, hinv21, h_v62⟩ growing hG carrying h_v12 h_v16 h_v19 h_v59 h_v61 dropping he_v62 hinv20 e_v62 s20
    store_step with Store.apply_rep s21 v62 v12 _ _ hinv21 h64 h_v62 h_v12 (by ns_tac) (by ns_tac) as ⟨v63, s22, hinv22, h_v63⟩ growing hG carrying h_v12 h_v16 h_v19 h_v59 h_v61 dropping h_v62 hinv21 s21 v62
    store_step with Store.apply_rep s22 v63 v19 _ _ hinv22 h64 h_v63 h_v19 (by ns_tac) (by ns_tac) as ⟨v64, s23, hinv23, h_v64⟩ growing hG carrying h_v12 h_v16 h_v59 h_v61 dropping h_v19 h_v63 hinv22 s22 v19 v63
    store_step with Store.apply_rep s23 v61 v64 _ _ hinv23 h64 h_v61 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s24, hinv24, h_v65⟩ growing hG carrying h_v12 h_v16 h_v59 dropping h_v61 h_v64 hinv23 s23 v61 v64
    step as ⟨e_v66, he_v66⟩
    store_step with CtorSpec.eo_forall.construct s24 e_v66 (by rw [he_v66]; exact empty_args) hinv24 h64 as ⟨v66, s25, hinv25, h_v66⟩ growing hG carrying h_v12 h_v16 h_v59 h_v65 dropping he_v66 hinv24 e_v66 s24
    store_step with Store.apply_rep s25 v66 v12 _ _ hinv25 h64 h_v66 h_v12 (by ns_tac) (by ns_tac) as ⟨v67, s26, hinv26, h_v67⟩ growing hG carrying h_v16 h_v59 h_v65 dropping h_v12 h_v66 hinv25 s25 v12 v66
    store_step with Store.apply_rep s26 v67 v16 _ _ hinv26 h64 h_v67 h_v16 (by ns_tac) (by ns_tac) as ⟨v68, s27, hinv27, h_v68⟩ growing hG carrying h_v59 h_v65 dropping h_v16 h_v67 hinv26 s26 v16 v67
    store_step with Store.apply_rep s27 v65 v68 _ _ hinv27 h64 h_v65 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s28, hinv28, h_v69⟩ growing hG carrying h_v59 dropping h_v65 h_v68 hinv27 s27 v65 v68
    store_step with Store.apply_rep s28 v59 v69 _ _ hinv28 h64 h_v59 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s29, hinv29, h_v70⟩ growing hG carrying dropping h_v59 h_v69 hinv28 s28 v59 v69
    req_done hinv29 hG with h_v70 using hq_v49)
  store_step with h_req_v71 as ⟨v71, s30, hinv30, h_v71⟩ growing hG carrying dropping h_req_v71 h_v12 h_v16 h_v19 h_v22 h_v49 h_v50 hinv9 s9 v12 v16 v19 v22 v49 v50
  case_done hinv30 hG with h_v71 in EoCases.__eo_prog_quant_miniscope_ite.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19 hn_v21 hn_v22 hn_v25 hn_v26 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43 hn_v45 hn_v46

/-- logos's `__eo_prog_quant_miniscope_ite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2dminiscope_2dite.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_miniscope_ite x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_miniscope_ite.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_miniscope_ite
  unfold EoCases.__eo_prog_quant_miniscope_ite.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2dminiscope_2dite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2dminiscope_2dite s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_miniscope_ite x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2dminiscope_2dite.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2dminiscope_2dite
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_miniscope_ite.case_0

theorem eo__24eo_5fprog_5fquant_2dminiscope_2dite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2dminiscope_2dite.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2dminiscope_2dite
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2dminiscope_2dite s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_miniscope_ite x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2dminiscope_2dite_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_miniscope_or.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_miniscope_or.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_miniscope_or.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_miniscope_or.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_or.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_or.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_miniscope_or.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_miniscope_or.case_0
  store_step with ih.eo__24is_5fquant_5fminiscope_5for s2 v12 v9 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_v12 h_v9 h_v2 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 h_v14 dropping hinv3 s3
  have h_req_v22 := (show requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor s4 v14 v15 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v14 v15 with h_v14 h_v15 using hinv4 hG
    req_stuck h_v14 as hq_v14 using hinv4 hG
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__3d.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 h_v15 he_v16 hinv4 e_v16 s4 v14 v15
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo_forall.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 dropping he_v17 hinv5 e_v17 s5
    store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v16 dropping h_v12 h_v17 hinv6 s6 v12 v17
    store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v16 dropping h_v18 h_v9 hinv7 s7 v18 v9
    store_step with Store.apply_rep s8 v16 v19 _ _ hinv8 h64 h_v16 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 dropping h_v16 h_v19 hinv8 s8 v16 v19
    store_step with Store.apply_rep s9 v20 v2 _ _ hinv9 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_v2 h_v20 hinv9 s9 v2 v20
    req_done hinv10 hG with h_v21 using hq_v14)
  store_step with h_req_v22 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying dropping h_req_v22 h_v12 h_v14 h_v15 h_v2 h_v9 hinv4 s4 v12 v14 v15 v2 v9
  case_done hinv11 hG with h_v22 in EoCases.__eo_prog_quant_miniscope_or.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_quant_miniscope_or` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2dminiscope_2dor.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_miniscope_or x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_miniscope_or.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_miniscope_or
  unfold EoCases.__eo_prog_quant_miniscope_or.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2dminiscope_2dor_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2dminiscope_2dor s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_miniscope_or x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2dminiscope_2dor.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2dminiscope_2dor
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_miniscope_or.case_0

theorem eo__24eo_5fprog_5fquant_2dminiscope_2dor_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2dminiscope_2dor.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2dminiscope_2dor
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2dminiscope_2dor s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_miniscope_or x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2dminiscope_2dor_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2dunused_2dvars_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2dunused_2dvars s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_unused_vars.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_unused_vars.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2dunused_2dvars
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_unused_vars.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_unused_vars.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_unused_vars.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_unused_vars.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_unused_vars.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_eq s2 e_v14 (by rw [he_v14]; rfl) h_v11 h_v13 hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v13 he_v14 hinv2 e_v14 s2 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_exists.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v14 dropping he_v15 hinv3 e_v15 s3
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_eq s4 e_v16 (by rw [he_v16]; rfl) h_v11 h_v15 hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v14 dropping h_v15 he_v16 hinv4 e_v16 s4 v15
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_or s5 e_v17 (by rw [he_v17]; rfl) h_v14 h_v16 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v14 h_v16 he_v17 hinv5 e_v17 s5 v14 v16
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v17 dropping hinv6 s6
  have h_req_v31 := (show requires_1_eo__24eo_5fprog_5fquant_2dunused_2dvars s7 v17 v18 v11 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fquant_2dunused_2dvars
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v17 v18 with h_v17 h_v18 using hinv7 hG
    req_stuck h_v17 as hq_v17 using hinv7 hG
    store_step with Store.apply_rep s7 v11 v12 _ _ hinv7 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v17 h_v18 hinv7 s7 v17 v18
    store_step with Store.apply_rep s8 v19 v9 _ _ hinv8 h64 h_v19 h_v9 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v19 hinv8 s8 v19
    store_step with ih.eo__24get_5funused_5fvars s9 v20 v2 _ _ hinv9 h64 (hG.rem hrem) h_v20 h_v2 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v20 hinv9 s9 v20
    step as ⟨e_v22, he_v22⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s10 e_v22 (by rw [he_v22]; exact empty_args) hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v21 dropping he_v22 hinv10 e_v22 s10
    store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s11 v2 v21 v22 _ _ _ hinv11 h64 (hG.rem hrem) h_v2 h_v21 h_v22 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v21 h_v22 hinv11 s11 v21 v22
    store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 h_v23 dropping hinv12 s12
    have h_req_v30 := (show requires_0_eo__24eo_5fprog_5fquant_2dunused_2dvars s13 v23 v24 v11 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s13.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fquant_2dunused_2dvars
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s13
      req_same v23 v24 with h_v23 h_v24 using hinv13 hG
      req_stuck h_v23 as hq_v23 using hinv13 hG
      step as ⟨e_v25, he_v25⟩
      store_step with CtorSpec.eo__3d.construct s13 e_v25 (by rw [he_v25]; exact empty_args) hinv13 h64 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v23 h_v24 he_v25 hinv13 e_v25 s13 v23 v24
      store_step with Store.apply_rep s14 v11 v12 _ _ hinv14 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v2 h_v9 h_v25 dropping h_v11 h_v12 hinv14 s14 v11 v12
      store_step with Store.apply_rep s15 v26 v9 _ _ hinv15 h64 h_v26 h_v9 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v2 h_v25 dropping h_v26 h_v9 hinv15 s15 v26 v9
      store_step with Store.apply_rep s16 v25 v27 _ _ hinv16 h64 h_v25 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v2 dropping h_v25 h_v27 hinv16 s16 v25 v27
      store_step with Store.apply_rep s17 v28 v2 _ _ hinv17 h64 h_v28 h_v2 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying dropping h_v2 h_v28 hinv17 s17 v2 v28
      req_done hinv18 hG with h_v29 using hq_v23)
    store_step with h_req_v30 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying dropping h_req_v30 h_v11 h_v12 h_v2 h_v23 h_v24 h_v9 hinv13 s13 v11 v12 v2 v23 v24 v9
    req_done hinv19 hG with h_v30 using hq_v17)
  store_step with h_req_v31 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying dropping h_req_v31 h_v11 h_v12 h_v17 h_v18 h_v2 h_v9 hinv7 s7 v11 v12 v17 v18 v2 v9
  case_done hinv20 hG with h_v31 in EoCases.__eo_prog_quant_unused_vars.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_quant_unused_vars` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2dunused_2dvars.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_unused_vars x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_unused_vars.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_unused_vars
  unfold EoCases.__eo_prog_quant_unused_vars.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2dunused_2dvars_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2dunused_2dvars s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_unused_vars x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2dunused_2dvars.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2dunused_2dvars
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2dunused_2dvars_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_unused_vars.case_0

theorem eo__24eo_5fprog_5fquant_2dunused_2dvars_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2dunused_2dvars.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2dunused_2dvars
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2dunused_2dvars s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_unused_vars x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2dunused_2dvars_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_var_elim_eq.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_var_elim_eq.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_v2 h_v9 h_v16 h_v18 h_v19 dropping h_v11 h_v12 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v12 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_v2 h_v9 h_v16 h_v19 dropping h_v18 h_v20 he_v21 hinv3 e_v21 s3 v18 v20
  pat_same v16 v21 with h_v16 h_v21 using hinv4 else hinv4 hG in EoCases.__eo_prog_quant_var_elim_eq.case_0
  store_step with ih.eo__24mk_5fquant_5fvar_5felim_5feq s4 v19 v9 _ _ hinv4 h64 (hG.rem hrem) h_v19 h_v9 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v2 h_v9 h_v19 dropping h_v16 h_v21 hinv4 s4 v16 v21
  have h_req_v33 := (show requires_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq s5 v22 v2 v19 v9 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v22 v2 with h_v22 h_v2 using hinv5 hG
    req_stuck h_v22 as hq_v22 using hinv5 hG
    step as ⟨e_v23, he_v23⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v23 (by rw [he_v23]; exact empty_args) hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_v2 h_v9 h_v19 dropping h_v22 he_v23 hinv5 e_v23 s5 v22
    step as ⟨e_v24, he_v24⟩
    store_step with CtorSpec.eo_forall.construct s6 e_v24 (by rw [he_v24]; exact empty_args) hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_v2 h_v9 h_v19 h_v23 dropping he_v24 hinv6 e_v24 s6
    step as ⟨e_v25, he_v25⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s7 e_v25 (by rw [he_v25]; exact empty_args) hinv7 h64 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_v2 h_v9 h_v19 h_v23 h_v24 dropping he_v25 hinv7 e_v25 s7
    store_step with Store.apply_rep s8 v25 v19 _ _ hinv8 h64 h_v25 h_v19 (by ns_tac) (by ns_tac) as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_v2 h_v9 h_v23 h_v24 dropping h_v19 h_v25 hinv8 s8 v19 v25
    step as ⟨e_v27, he_v27⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s9 e_v27 (by rw [he_v27]; exact empty_args) hinv9 h64 as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying h_v2 h_v9 h_v23 h_v24 h_v26 dropping he_v27 hinv9 e_v27 s9
    store_step with Store.apply_rep s10 v26 v27 _ _ hinv10 h64 h_v26 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying h_v2 h_v9 h_v23 h_v24 dropping h_v26 h_v27 hinv10 s10 v26 v27
    store_step with Store.apply_rep s11 v24 v28 _ _ hinv11 h64 h_v24 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s12, hinv12, h_v29⟩ growing hG carrying h_v2 h_v9 h_v23 dropping h_v24 h_v28 hinv11 s11 v24 v28
    store_step with Store.apply_rep s12 v29 v9 _ _ hinv12 h64 h_v29 h_v9 (by ns_tac) (by ns_tac) as ⟨v30, s13, hinv13, h_v30⟩ growing hG carrying h_v2 h_v23 dropping h_v29 h_v9 hinv12 s12 v29 v9
    store_step with Store.apply_rep s13 v23 v30 _ _ hinv13 h64 h_v23 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying h_v2 dropping h_v23 h_v30 hinv13 s13 v23 v30
    store_step with Store.apply_rep s14 v31 v2 _ _ hinv14 h64 h_v31 h_v2 (by ns_tac) (by ns_tac) as ⟨v32, s15, hinv15, h_v32⟩ growing hG carrying dropping h_v2 h_v31 hinv14 s14 v2 v31
    req_done hinv15 hG with h_v32 using hq_v22)
  store_step with h_req_v33 as ⟨v33, s16, hinv16, h_v33⟩ growing hG carrying dropping h_req_v33 h_v19 h_v2 h_v22 h_v9 hinv5 s5 v19 v2 v22 v9
  case_done hinv16 hG with h_v33 in EoCases.__eo_prog_quant_var_elim_eq.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

/-- logos's `__eo_prog_quant_var_elim_eq` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_2dvar_2delim_2deq.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_var_elim_eq x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_var_elim_eq.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_var_elim_eq
  unfold EoCases.__eo_prog_quant_var_elim_eq.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_var_elim_eq x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_2dvar_2delim_2deq.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_var_elim_eq.case_0

theorem eo__24eo_5fprog_5fquant_2dvar_2delim_2deq_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_2dvar_2delim_2deq.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_2dvar_2delim_2deq
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_var_elim_eq x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fquant_5fvar_5freordering_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fquant_5fvar_5freordering s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_quant_var_reordering.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_quant_var_reordering.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fquant_5fvar_5freordering
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_var_reordering.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_quant_var_reordering.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  pat_unapply h_v2 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_forall.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_v9 h_v12 h_v16 h_v18 h_v19 dropping h_v11 h_v13 h_v15 h_v2 he_v20 hinv2 e_v20 s2 v11 v13 v15 v2
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  pat_same v16 v9 with h_v16 h_v9 using hinv3 else hinv3 hG in EoCases.__eo_prog_quant_var_reordering.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_v9 h_v12 h_v19 dropping h_v16 h_v18 h_v20 he_v21 hinv3 e_v21 s3 v16 v18 v20
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_meq n ih.eo__24eo_5fis_5flist_5fnil s4 e_v22 (by rw [he_v22]; rfl) h_v21 h_v12 h_v19 hinv4 h64 (hG.rem hrem) (by not_left_tac) (by unique_nil_tac) as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_v9 h_v12 h_v19 dropping h_v21 he_v22 hinv4 e_v22 s4 v21
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_v9 h_v12 h_v19 h_v22 dropping hinv5 s5
  have h_req_v33 := (show requires_0_eo__24eo_5fprog_5fquant_5fvar_5freordering s6 v22 v23 v12 v9 v19 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fquant_5fvar_5freordering
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v22 v23 with h_v22 h_v23 using hinv6 hG
    req_stuck h_v22 as hq_v22 using hinv6 hG
    step as ⟨e_v24, he_v24⟩
    store_step with CtorSpec.eo__3d.construct s6 e_v24 (by rw [he_v24]; exact empty_args) hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_v9 h_v12 h_v19 dropping h_v22 h_v23 he_v24 hinv6 e_v24 s6 v22 v23
    step as ⟨e_v25, he_v25⟩
    store_step with CtorSpec.eo_forall.construct s7 e_v25 (by rw [he_v25]; exact empty_args) hinv7 h64 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_v9 h_v12 h_v19 h_v24 dropping he_v25 hinv7 e_v25 s7
    store_step with Store.apply_rep s8 v25 v12 _ _ hinv8 h64 h_v25 h_v12 (by ns_tac) (by ns_tac) as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_v9 h_v19 h_v24 dropping h_v12 h_v25 hinv8 s8 v12 v25
    store_step with Store.apply_rep s9 v26 v9 _ _ hinv9 h64 h_v26 h_v9 (by ns_tac) (by ns_tac) as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying h_v9 h_v19 h_v24 dropping h_v26 hinv9 s9 v26
    store_step with Store.apply_rep s10 v24 v27 _ _ hinv10 h64 h_v24 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying h_v9 h_v19 dropping h_v24 h_v27 hinv10 s10 v24 v27
    step as ⟨e_v29, he_v29⟩
    store_step with CtorSpec.eo_forall.construct s11 e_v29 (by rw [he_v29]; exact empty_args) hinv11 h64 as ⟨v29, s12, hinv12, h_v29⟩ growing hG carrying h_v9 h_v19 h_v28 dropping he_v29 hinv11 e_v29 s11
    store_step with Store.apply_rep s12 v29 v19 _ _ hinv12 h64 h_v29 h_v19 (by ns_tac) (by ns_tac) as ⟨v30, s13, hinv13, h_v30⟩ growing hG carrying h_v9 h_v28 dropping h_v19 h_v29 hinv12 s12 v19 v29
    store_step with Store.apply_rep s13 v30 v9 _ _ hinv13 h64 h_v30 h_v9 (by ns_tac) (by ns_tac) as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying h_v28 dropping h_v30 h_v9 hinv13 s13 v30 v9
    store_step with Store.apply_rep s14 v28 v31 _ _ hinv14 h64 h_v28 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s15, hinv15, h_v32⟩ growing hG carrying dropping h_v28 h_v31 hinv14 s14 v28 v31
    req_done hinv15 hG with h_v32 using hq_v22)
  store_step with h_req_v33 as ⟨v33, s16, hinv16, h_v33⟩ growing hG carrying dropping h_req_v33 h_v12 h_v19 h_v22 h_v23 h_v9 hinv6 s6 v12 v19 v22 v23 v9
  case_done hinv16 hG with h_v33 in EoCases.__eo_prog_quant_var_reordering.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

/-- logos's `__eo_prog_quant_var_reordering` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fquant_5fvar_5freordering.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_quant_var_reordering x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_quant_var_reordering.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_quant_var_reordering
  unfold EoCases.__eo_prog_quant_var_reordering.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fquant_5fvar_5freordering_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fquant_5fvar_5freordering s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_quant_var_reordering x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fquant_5fvar_5freordering.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fquant_5fvar_5freordering
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fquant_5fvar_5freordering_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_quant_var_reordering.case_0

theorem eo__24eo_5fprog_5fquant_5fvar_5freordering_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fquant_5fvar_5freordering.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fquant_5fvar_5freordering
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fquant_5fvar_5freordering s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_quant_var_reordering x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fquant_5fvar_5freordering_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- The body of the constant `$eo_prog_re-all-elim` builds logos's `__eo_prog_re_all_elim`. -/
theorem body_eo__24eo_5fprog_5fre_2dall_2delim_spec (n : Nat) (ih : Specs n) (s : Store)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) :
    body_eo__24eo_5fprog_5fre_2dall_2delim s ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t __eo_prog_re_all_elim
      | core.result.Result.Err _ => True ⦄div := by
  unfold body_eo__24eo_5fprog_5fre_2dall_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying dropping
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2eall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_v0 dropping
  store_step with Store.apply_rep s2 v0 v1 _ _ hinv2 h64 h_v0 h_v1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v0 h_v1 dropping
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 h_v1 h_v2 dropping
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v0 h_v1 h_v2 h_v3 dropping
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v0 h_v1 h_v2 h_v3 h_v4 dropping
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 dropping
  simp only [WP.dspec_ok, WP.uncurry'_pair]
  exact ⟨hinv7, hG, Represents.rep_of_eq h_v6 (by unfold __eo_prog_re_all_elim; rfl)⟩

theorem eo__24eo_5fprog_5fre_2dall_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dall_2delim.Spec n := by
  intro s hinv h64 hrem
  unfold eo__24eo_5fprog_5fre_2dall_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dall_2delim s1) (fun s' t => Represents.rep s' t (__eo_prog_re_all_elim))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dall_2delim_spec m (ih m hm) s1 hinv1 h64 hrem1))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_concat_star_repeat.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_concat_star_repeat.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v2 h_v4 hinv5 s5 v2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 dropping he_v6 hinv6 e_v6 s6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a1 _ _ hinv8 h64 h_v7 h_a1 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 h_v6 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v6 v8 _ _ hinv9 h64 h_v6 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 dropping h_v6 h_v8 hinv9 s9 v6 v8
  store_step with Store.apply_rep s10 v9 a2 _ _ hinv10 h64 h_v9 h_a2 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 dropping h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v10 h_v5 hinv11 s11 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s12 e_v12 (by rw [he_v12]; rfl) h_v1 h_a0 h_v11 hinv12 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 h_v11 he_v12 hinv12 e_v12 s12 v1 v11
  store_step with Store.apply_mk_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v12 hinv13 s13 v0 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping he_v14 hinv14 e_v14 s14
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 h_v14 dropping he_v15 hinv15 e_v15 s15
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 h_v14 h_v15 dropping he_v16 hinv16 e_v16 s16
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 h_v14 h_v15 h_v16 dropping he_v17 hinv17 e_v17 s17
  store_step with Store.apply_rep s18 v17 a1 _ _ hinv18 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a2 h_v13 h_v14 h_v15 h_v16 dropping h_a1 h_v17 hinv18 s18 v17
  store_step with Store.apply_rep s19 v16 v18 _ _ hinv19 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a2 h_v13 h_v14 h_v15 dropping h_v16 h_v18 hinv19 s19 v16 v18
  store_step with Store.apply_rep s20 v19 a2 _ _ hinv20 h64 h_v19 h_a2 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_v13 h_v14 h_v15 dropping h_a2 h_v19 hinv20 s20 v19
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s21 e_v21 (by rw [he_v21]; rfl) h_v15 h_a0 h_v20 hinv21 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_v13 h_v14 dropping h_a0 h_v15 h_v20 he_v21 hinv21 e_v21 s21 v15 v20
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s22 e_v22 (by rw [he_v22]; rfl) h_v14 h_v21 hinv22 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_nil_apply_eo_re_2e_2b_2b as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_v13 dropping h_v14 h_v21 he_v22 hinv22 e_v22 s22 v14 v21
  store_step with Store.apply_mk_rep s23 v13 v22 _ _ hinv23 h64 h_v13 h_v22 as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying dropping h_v13 h_v22 hinv23 s23 v13 v22
  case_done hinv24 hG with h_v23 in EoCases.__eo_prog_re_concat_star_repeat.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_re_concat_star_repeat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_re_concat_star_repeat x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_concat_star_repeat.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_concat_star_repeat
  unfold EoCases.__eo_prog_re_concat_star_repeat.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_star_repeat x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_concat_star_repeat.case_0

theorem eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_re_concat_star_repeat x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2drepeat_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_concat_star_swap.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_concat_star_swap.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v2 h_v4 hinv5 s5 v2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 dropping h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v5 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 dropping h_v5 h_v8 hinv9 s9 v5 v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s10 e_v10 (by rw [he_v10]; rfl) h_v1 h_a0 h_v9 hinv10 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 h_v9 he_v10 hinv10 e_v10 s10 v1 v9
  store_step with Store.apply_mk_rep s11 v0 v10 _ _ hinv11 h64 h_v0 h_v10 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v10 hinv11 s11 v0 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 dropping he_v12 hinv12 e_v12 s12
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s13 e_v13 (by rw [he_v13]; exact empty_args) hinv13 h64 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v12 dropping he_v13 hinv13 e_v13 s13
  store_step with Store.apply_rep s14 v13 a1 _ _ hinv14 h64 h_v13 h_a1 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v12 dropping h_v13 hinv14 s14 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v12 h_v14 dropping he_v15 hinv15 e_v15 s15
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v12 h_v14 h_v15 dropping he_v16 hinv16 e_v16 s16
  store_step with Store.apply_rep s17 v16 a1 _ _ hinv17 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a2 h_v11 h_v12 h_v14 h_v15 dropping h_a1 h_v16 hinv17 s17 v16
  store_step with Store.apply_rep s18 v15 v17 _ _ hinv18 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a2 h_v11 h_v12 h_v14 dropping h_v15 h_v17 hinv18 s18 v15 v17
  store_step with Store.apply_rep s19 v18 a2 _ _ hinv19 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_v11 h_v12 h_v14 dropping h_a2 h_v18 hinv19 s19 v18
  store_step with Store.apply_rep s20 v14 v19 _ _ hinv20 h64 h_v14 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_v11 h_v12 dropping h_v14 h_v19 hinv20 s20 v14 v19
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s21 e_v21 (by rw [he_v21]; rfl) h_v12 h_a0 h_v20 hinv21 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_v11 dropping h_a0 h_v12 h_v20 he_v21 hinv21 e_v21 s21 v12 v20
  store_step with Store.apply_mk_rep s22 v11 v21 _ _ hinv22 h64 h_v11 h_v21 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying dropping h_v11 h_v21 hinv22 s22 v11 v21
  case_done hinv23 hG with h_v22 in EoCases.__eo_prog_re_concat_star_swap.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_re_concat_star_swap` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_re_concat_star_swap x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_concat_star_swap.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_concat_star_swap
  unfold EoCases.__eo_prog_re_concat_star_swap.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_star_swap x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_concat_star_swap.case_0

theorem eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_re_concat_star_swap x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dswap_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2ddiff_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2ddiff_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_diff_elim.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_diff_elim.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2ddiff_2delim
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2ediff.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_re_2einter.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 h_v4 dropping h_a0 h_v5 hinv6 s6 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_re_2einter.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 h_v4 h_v6 dropping he_v7 hinv7 e_v7 s7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v4 h_v6 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v4 h_v6 h_v7 dropping h_a1 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v4 h_v6 dropping h_v7 h_v9 hinv10 s10 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_re_2eall.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v4 h_v6 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v4 h_v6 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_rep s13 v6 v12 _ _ hinv13 h64 h_v6 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v4 dropping h_v12 h_v6 hinv13 s13 v12 v6
  store_step with Store.apply_rep s14 v4 v13 _ _ hinv14 h64 h_v4 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v4 hinv14 s14 v13 v4
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_re_diff_elim.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_re_diff_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2ddiff_2delim.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_re_diff_elim x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_diff_elim.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_diff_elim
  unfold EoCases.__eo_prog_re_diff_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2ddiff_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fre_2ddiff_2delim s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_diff_elim x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2ddiff_2delim.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fre_2ddiff_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2ddiff_2delim_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_diff_elim.case_0

theorem eo__24eo_5fprog_5fre_2ddiff_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2ddiff_2delim.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fre_2ddiff_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2ddiff_2delim s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_re_diff_elim x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2ddiff_2delim_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2deq_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2deq_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_eq_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_eq_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2deq_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_re_eq_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_re_eq_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_eq_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_eq_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_eq_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_eq_elim.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  store_step with Store.apply_rep s3 v14 v12 _ _ hinv3 h64 h_v14 h_v12 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 hinv3 s3 v14
  store_step with Store.apply_rep s4 v15 v9 _ _ hinv4 h64 h_v15 h_v9 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v15 hinv4 s4 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 h_v16 dropping he_v17 hinv5 e_v17 s5
  store_step with ih.eo__24is_5fclosed_5frec s6 v16 v17 _ _ hinv6 h64 (hG.rem hrem) h_v16 h_v17 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v16 h_v17 hinv6 s6 v16 v17
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 dropping hinv7 s7
  have h_req_v58 := (show requires_3_eo__24eo_5fprog_5fre_2deq_2delim s8 v18 v19 v12 v9 v2 ⦃ r s' => s'.Inv ∧ s8.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_3_eo__24eo_5fprog_5fre_2deq_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s8
    req_same v18 v19 with h_v18 h_v19 using hinv8 hG
    req_stuck h_v18 as hq_v18 using hinv8 hG
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo_forall.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v18 h_v19 he_v20 hinv8 e_v20 s8 v18 v19
    step as ⟨e_v21, he_v21⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s9 e_v21 (by rw [he_v21]; exact empty_args) hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 dropping he_v21 hinv9 e_v21 s9
    step as ⟨e_v22, he_v22⟩
    try simp only [eostring.EoString.from_code_points, Std.bind_ok]
    store_step with Store.literal_str_vec_spec s10 _ _ rfl hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 h_v21 dropping hinv10 s10
    replace h_v22 := Represents.rep_of_eq h_v22 (y := Eo.Term.String (SmtEval.native_string_lit "@var.re_eq")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v22]; decide)
    step as ⟨e_v23, he_v23⟩
    store_step with CtorSpec.eo_Seq.construct s11 e_v23 (by rw [he_v23]; exact empty_args) hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 h_v21 h_v22 dropping he_v22 he_v23 hinv11 e_v22 e_v23 s11
    step as ⟨e_v24, he_v24⟩
    store_step with CtorSpec.eo_Char.construct s12 e_v24 (by rw [he_v24]; exact empty_args) hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 h_v21 h_v22 h_v23 dropping he_v24 hinv12 e_v24 s12
    store_step with Store.apply_rep s13 v23 v24 _ _ hinv13 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 h_v21 h_v22 dropping h_v23 h_v24 hinv13 s13 v23 v24
    step as ⟨e_v26, he_v26⟩
    store_step with CtorSpec.eo__24emb_5fVar.construct s14 e_v26 (by rw [he_v26]; rfl) h_v22 h_v25 hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 h_v21 dropping h_v22 h_v25 he_v26 hinv14 e_v26 s14 v22 v25
    store_step with Store.apply_rep s15 v21 v26 _ _ hinv15 h64 h_v21 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 dropping h_v21 h_v26 hinv15 s15 v21 v26
    step as ⟨e_v28, he_v28⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s16 e_v28 (by rw [he_v28]; exact empty_args) hinv16 h64 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 h_v27 dropping he_v28 hinv16 e_v28 s16
    store_step with Store.apply_rep s17 v27 v28 _ _ hinv17 h64 h_v27 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_v2 h_v9 h_v12 h_v20 dropping h_v27 h_v28 hinv17 s17 v27 v28
    store_step with Store.apply_rep s18 v20 v29 _ _ hinv18 h64 h_v20 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v20 h_v29 hinv18 s18 v20 v29
    step as ⟨e_v31, he_v31⟩
    store_step with CtorSpec.eo__3d.construct s19 e_v31 (by rw [he_v31]; exact empty_args) hinv19 h64 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 dropping he_v31 hinv19 e_v31 s19
    step as ⟨e_v32, he_v32⟩
    store_step with CtorSpec.eo_str_2ein_5fre.construct s20 e_v32 (by rw [he_v32]; exact empty_args) hinv20 h64 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 dropping he_v32 hinv20 e_v32 s20
    step as ⟨e_v33, he_v33⟩
    try simp only [eostring.EoString.from_code_points, Std.bind_ok]
    store_step with Store.literal_str_vec_spec s21 _ _ rfl hinv21 h64 as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 h_v32 dropping hinv21 s21
    replace h_v33 := Represents.rep_of_eq h_v33 (y := Eo.Term.String (SmtEval.native_string_lit "@var.re_eq")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v33]; decide)
    step as ⟨e_v34, he_v34⟩
    store_step with CtorSpec.eo_Seq.construct s22 e_v34 (by rw [he_v34]; exact empty_args) hinv22 h64 as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 h_v32 h_v33 dropping he_v33 he_v34 hinv22 e_v33 e_v34 s22
    step as ⟨e_v35, he_v35⟩
    store_step with CtorSpec.eo_Char.construct s23 e_v35 (by rw [he_v35]; exact empty_args) hinv23 h64 as ⟨v35, s24, hinv24, h_v35⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 h_v32 h_v33 h_v34 dropping he_v35 hinv23 e_v35 s23
    store_step with Store.apply_rep s24 v34 v35 _ _ hinv24 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s25, hinv25, h_v36⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 h_v32 h_v33 dropping h_v34 h_v35 hinv24 s24 v34 v35
    step as ⟨e_v37, he_v37⟩
    store_step with CtorSpec.eo__24emb_5fVar.construct s25 e_v37 (by rw [he_v37]; rfl) h_v33 h_v36 hinv25 h64 as ⟨v37, s26, hinv26, h_v37⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 h_v32 dropping h_v33 h_v36 he_v37 hinv25 e_v37 s25 v33 v36
    store_step with Store.apply_rep s26 v32 v37 _ _ hinv26 h64 h_v32 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s27, hinv27, h_v38⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 dropping h_v32 h_v37 hinv26 s26 v32 v37
    store_step with Store.apply_rep s27 v38 v12 _ _ hinv27 h64 h_v38 h_v12 (by ns_tac) (by ns_tac) as ⟨v39, s28, hinv28, h_v39⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v31 dropping h_v38 hinv27 s27 v38
    store_step with Store.apply_rep s28 v31 v39 _ _ hinv28 h64 h_v31 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s29, hinv29, h_v40⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 dropping h_v31 h_v39 hinv28 s28 v31 v39
    step as ⟨e_v41, he_v41⟩
    store_step with CtorSpec.eo_str_2ein_5fre.construct s29 e_v41 (by rw [he_v41]; exact empty_args) hinv29 h64 as ⟨v41, s30, hinv30, h_v41⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 dropping he_v41 hinv29 e_v41 s29
    step as ⟨e_v42, he_v42⟩
    try simp only [eostring.EoString.from_code_points, Std.bind_ok]
    store_step with Store.literal_str_vec_spec s30 _ _ rfl hinv30 h64 as ⟨v42, s31, hinv31, h_v42⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 h_v41 dropping hinv30 s30
    replace h_v42 := Represents.rep_of_eq h_v42 (y := Eo.Term.String (SmtEval.native_string_lit "@var.re_eq")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v42]; decide)
    step as ⟨e_v43, he_v43⟩
    store_step with CtorSpec.eo_Seq.construct s31 e_v43 (by rw [he_v43]; exact empty_args) hinv31 h64 as ⟨v43, s32, hinv32, h_v43⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 h_v41 h_v42 dropping he_v42 he_v43 hinv31 e_v42 e_v43 s31
    step as ⟨e_v44, he_v44⟩
    store_step with CtorSpec.eo_Char.construct s32 e_v44 (by rw [he_v44]; exact empty_args) hinv32 h64 as ⟨v44, s33, hinv33, h_v44⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 h_v41 h_v42 h_v43 dropping he_v44 hinv32 e_v44 s32
    store_step with Store.apply_rep s33 v43 v44 _ _ hinv33 h64 h_v43 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s34, hinv34, h_v45⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 h_v41 h_v42 dropping h_v43 h_v44 hinv33 s33 v43 v44
    step as ⟨e_v46, he_v46⟩
    store_step with CtorSpec.eo__24emb_5fVar.construct s34 e_v46 (by rw [he_v46]; rfl) h_v42 h_v45 hinv34 h64 as ⟨v46, s35, hinv35, h_v46⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 h_v41 dropping h_v42 h_v45 he_v46 hinv34 e_v46 s34 v42 v45
    store_step with Store.apply_rep s35 v41 v46 _ _ hinv35 h64 h_v41 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s36, hinv36, h_v47⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 dropping h_v41 h_v46 hinv35 s35 v41 v46
    store_step with Store.apply_rep s36 v47 v9 _ _ hinv36 h64 h_v47 h_v9 (by ns_tac) (by ns_tac) as ⟨v48, s37, hinv37, h_v48⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 h_v40 dropping h_v47 hinv36 s36 v47
    store_step with Store.apply_rep s37 v40 v48 _ _ hinv37 h64 h_v40 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s38, hinv38, h_v49⟩ growing hG carrying h_v2 h_v9 h_v12 h_v30 dropping h_v40 h_v48 hinv37 s37 v40 v48
    store_step with Store.apply_rep s38 v30 v49 _ _ hinv38 h64 h_v30 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s39, hinv39, h_v50⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v30 h_v49 hinv38 s38 v30 v49
    have h_req_v57 := (show requires_0_eo__24eo_5fprog_5fre_2deq_2delim s39 v2 v50 v12 v9 ⦃ r s' => s'.Inv ∧ s39.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_0_eo__24eo_5fprog_5fre_2deq_2delim
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s39
      req_same v2 v50 with h_v2 h_v50 using hinv39 hG
      req_stuck h_v2 as hq_v2 using hinv39 hG
      step as ⟨e_v51, he_v51⟩
      store_step with CtorSpec.eo__3d.construct s39 e_v51 (by rw [he_v51]; exact empty_args) hinv39 h64 as ⟨v51, s40, hinv40, h_v51⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v50 he_v51 hinv39 e_v51 s39 v50
      step as ⟨e_v52, he_v52⟩
      store_step with CtorSpec.eo__3d.construct s40 e_v52 (by rw [he_v52]; exact empty_args) hinv40 h64 as ⟨v52, s41, hinv41, h_v52⟩ growing hG carrying h_v2 h_v9 h_v12 h_v51 dropping he_v52 hinv40 e_v52 s40
      store_step with Store.apply_rep s41 v52 v12 _ _ hinv41 h64 h_v52 h_v12 (by ns_tac) (by ns_tac) as ⟨v53, s42, hinv42, h_v53⟩ growing hG carrying h_v2 h_v9 h_v51 dropping h_v12 h_v52 hinv41 s41 v12 v52
      store_step with Store.apply_rep s42 v53 v9 _ _ hinv42 h64 h_v53 h_v9 (by ns_tac) (by ns_tac) as ⟨v54, s43, hinv43, h_v54⟩ growing hG carrying h_v2 h_v51 dropping h_v53 h_v9 hinv42 s42 v53 v9
      store_step with Store.apply_rep s43 v51 v54 _ _ hinv43 h64 h_v51 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s44, hinv44, h_v55⟩ growing hG carrying h_v2 dropping h_v51 h_v54 hinv43 s43 v51 v54
      store_step with Store.apply_rep s44 v55 v2 _ _ hinv44 h64 h_v55 h_v2 (by ns_tac) (by ns_tac) as ⟨v56, s45, hinv45, h_v56⟩ growing hG carrying dropping h_v2 h_v55 hinv44 s44 v2 v55
      req_done hinv45 hG with h_v56 using hq_v2)
    store_step with h_req_v57 as ⟨v57, s46, hinv46, h_v57⟩ growing hG carrying dropping h_req_v57 h_v12 h_v2 h_v50 h_v9 hinv39 s39 v12 v2 v50 v9
    req_done hinv46 hG with h_v57 using hq_v18)
  store_step with h_req_v58 as ⟨v58, s47, hinv47, h_v58⟩ growing hG carrying dropping h_req_v58 h_v12 h_v18 h_v19 h_v2 h_v9 hinv8 s8 v12 v18 v19 v2 v9
  case_done hinv47 hG with h_v58 in EoCases.__eo_prog_re_eq_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_re_eq_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2deq_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_eq_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_eq_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_eq_elim
  unfold EoCases.__eo_prog_re_eq_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2deq_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2deq_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_eq_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2deq_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2deq_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2deq_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_eq_elim.case_0

theorem eo__24eo_5fprog_5fre_2deq_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2deq_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2deq_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2deq_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_eq_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2deq_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_comp.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_comp.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dcomp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2ecomp.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v4 hinv5 s5 v2 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v6 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v6 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v6 h_v7 dropping h_a1 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v7 v10 _ _ hinv11 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v6 dropping h_v10 h_v7 hinv11 s11 v10 v7
  store_step with Store.apply_rep s12 v6 v11 _ _ hinv12 h64 h_v6 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying dropping h_v11 h_v6 hinv12 s12 v11 v6
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_re_in_comp.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_re_in_comp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dcomp.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_re_in_comp x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_comp.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_comp
  unfold EoCases.__eo_prog_re_in_comp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dcomp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fre_2din_2dcomp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_comp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dcomp.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dcomp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dcomp_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_in_comp.case_0

theorem eo__24eo_5fprog_5fre_2din_2dcomp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dcomp.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fre_2din_2dcomp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dcomp s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_re_in_comp x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dcomp_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dcstring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dcstring s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_cstring.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_cstring.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dcstring
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v4 hinv5 s5 v2 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v5 hinv6 s6 v0 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v6 dropping h_a0 h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v6 dropping h_a1 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v6 v9 _ _ hinv10 h64 h_v6 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_v6 h_v9 hinv10 s10 v6 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_re_in_cstring.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_re_in_cstring` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dcstring.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_re_in_cstring x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_cstring.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_cstring
  unfold EoCases.__eo_prog_re_in_cstring.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dcstring_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fre_2din_2dcstring s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_cstring x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dcstring.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dcstring
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dcstring_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_re_in_cstring.case_0

theorem eo__24eo_5fprog_5fre_2din_2dcstring_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dcstring.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fre_2din_2dcstring
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dcstring s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_re_in_cstring x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dcstring_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dempty
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v0 dropping h_a0 h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2enone.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v0 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v5 dropping hinv6 s6
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_v5 h_v6 hinv7 s7 v5 v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_re_in_empty.case_0 using hn_a0

/-- logos's `__eo_prog_re_in_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_in_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_empty
  unfold EoCases.__eo_prog_re_in_empty.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2din_2dempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_in_empty.case_0

theorem eo__24eo_5fprog_5fre_2din_2dempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2din_2dempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dempty s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_in_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dsigma_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dsigma s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_sigma.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_sigma.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dsigma
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 dropping h_v0 h_v4 hinv5 s5 v0 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v5 dropping he_v6 hinv6 e_v6 s6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2elen.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v5 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v5 h_v6 dropping h_a0 h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v6 v8 _ _ hinv9 h64 h_v6 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v5 dropping h_v6 h_v8 hinv9 s9 v6 v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 1#u32 (1) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v5 h_v9 dropping hinv10 s10
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v5 dropping h_v10 h_v9 hinv11 s11 v10 v9
  store_step with Store.apply_rep s12 v5 v11 _ _ hinv12 h64 h_v5 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying dropping h_v11 h_v5 hinv12 s12 v11 v5
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_re_in_sigma.case_0 using hn_a0

/-- logos's `__eo_prog_re_in_sigma` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dsigma.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_in_sigma x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_sigma.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_sigma
  unfold EoCases.__eo_prog_re_in_sigma.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dsigma_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2din_2dsigma s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dsigma.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dsigma
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dsigma_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_in_sigma.case_0

theorem eo__24eo_5fprog_5fre_2din_2dsigma_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dsigma.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2din_2dsigma
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dsigma s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_in_sigma x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dsigma_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_in_sigma_star.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_in_sigma_star.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v0 dropping h_a0 h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v0 h_v2 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v0 h_v2 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_v0 h_v6 hinv7 s7 v0 v6
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v7 dropping hinv8 s8
  store_step with Store.apply_rep s9 v7 v8 _ _ hinv9 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying dropping h_v7 h_v8 hinv9 s9 v7 v8
  case_done hinv10 hG with h_v9 in EoCases.__eo_prog_re_in_sigma_star.case_0 using hn_a0

/-- logos's `__eo_prog_re_in_sigma_star` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_re_in_sigma_star x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_in_sigma_star.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_in_sigma_star
  unfold EoCases.__eo_prog_re_in_sigma_star.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_in_sigma_star x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_re_in_sigma_star.case_0

theorem eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2din_2dsigma_2dstar.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fre_2din_2dsigma_2dstar
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_re_in_sigma_star x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2din_2dsigma_2dstar_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
