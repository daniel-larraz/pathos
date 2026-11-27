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

set_option maxHeartbeats 4000000 in
theorem case_0_eo__24chain_5fm_5fresolve_5ffinal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24chain_5fm_5fresolve_5ffinal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__chain_m_resolve_final.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__chain_m_resolve_final.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24chain_5fm_5fresolve_5ffinal
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_final.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__chain_m_resolve_final.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_final.case_0
  pat_unapply h_v2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_final.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__chain_m_resolve_final.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v5 h_v9 h_v11 h_v12 dropping h_v2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v2 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__chain_m_resolve_final.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_eq s2 e_v14 (by rw [he_v14]; rfl) h_a0 h_v12 hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v5 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  have h_ite_v22 := (show if_0_eo__24chain_5fm_5fresolve_5ffinal s3 v14 v5 v12 v9 a0 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24chain_5fm_5fresolve_5ffinal
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v14 with ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩ | ⟨hx_15, hbv_15⟩
    · ite_branch hbv_15
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_15 h_v5)
    · ite_branch hbv_15
      step as ⟨e_v15, he_v15⟩
      store_step with CtorSpec.eo_or.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v5 h_v9 h_v12 dropping h_v14 he_v15 e_v15 v14
      step as ⟨e_v16, he_v16⟩
      store_step with CtorSpec.eo_or.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v5 h_v9 h_v12 h_v15 dropping he_v16 e_v16
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo_or.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v5 h_v9 h_v12 h_v15 h_v16 dropping he_v17 hinv5 e_v17 s5
      store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_v5 h_v9 h_v15 h_v16 dropping h_v12 h_v17 hinv6 s6 v12 v17
      store_step with Store.apply_rep s7 v18 v9 _ _ hinv7 h64 h_v18 h_v9 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_v5 h_v15 h_v16 dropping h_v18 h_v9 hinv7 s7 v18 v9
      step as ⟨e_v20, he_v20⟩
      store_step with Store.builtin_spec_list_diff n ih.eo__24eo_5fis_5flist_5fnil s8 e_v20 (by rw [he_v20]; rfl) h_v16 h_a0 h_v19 hinv8 h64 (hG.rem hrem) op_not_left_eo_or op_unique_nil_eo_or as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v5 h_v15 dropping h_a0 h_v16 h_v19 he_v20 hinv8 e_v20 s8 v16 v19
      step as ⟨e_v21, he_v21⟩
      store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s9 e_v21 (by rw [he_v21]; rfl) h_v15 h_v20 h_v5 hinv9 h64 (hG.rem hrem) op_not_left_eo_or op_unique_nil_eo_or as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_v15 h_v20 h_v5 he_v21 hinv9 e_v21 s9 v15 v20 v5
      ite_done hinv10 hG with (eo_ite_false_rep _ hx_15 h_v21)
    · ite_branch hbv_15
      ite_stuck hinv3 hG with hx_15)
  store_step with h_ite_v22 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying dropping h_a0 h_ite_v22 h_v12 h_v14 h_v5 h_v9 hinv3 s3 v12 v14 v5 v9
  case_done hinv4 hG with h_v22 in EoCases.__chain_m_resolve_final.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

set_option maxHeartbeats 4000000 in
/-- logos's `__chain_m_resolve_final` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24chain_5fm_5fresolve_5ffinal.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __chain_m_resolve_final x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__chain_m_resolve_final.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __chain_m_resolve_final
  unfold EoCases.__chain_m_resolve_final.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24chain_5fm_5fresolve_5ffinal_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24chain_5fm_5fresolve_5ffinal s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__chain_m_resolve_final x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24chain_5fm_5fresolve_5ffinal.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24chain_5fm_5fresolve_5ffinal
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24chain_5fm_5fresolve_5ffinal_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__chain_m_resolve_final.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24chain_5fm_5fresolve_5ffinal_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24chain_5fm_5fresolve_5ffinal.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24chain_5fm_5fresolve_5ffinal
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24chain_5fm_5fresolve_5ffinal s1 a0 a1) (fun s' t => Represents.rep s' t (__chain_m_resolve_final x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24chain_5fm_5fresolve_5ffinal_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
