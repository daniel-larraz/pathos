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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_5
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_5
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_6
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_6
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_7
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_7
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_8
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_8
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3e.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3e.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_5
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_5
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 h_a3 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a3 dropping h_a2 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_a3 h_v3 hinv4 s4 v3
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

theorem case_0_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2 = some (__assoc_nil_nth y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24assoc_5fnil_5fnth
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_0
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__assoc_nil_nth.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a2 h_v5 dropping h_a0 h_a1 h_v1 h_v2 h_v4 v1 v2 v4
  pat_same a2 v6 with h_a2 h_v6 using hinv1 else hinv1 hG in EoCases.__assoc_nil_nth.case_0
  case_done hinv1 hG with h_v5 in EoCases.__assoc_nil_nth.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2 = some (__assoc_nil_nth y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24assoc_5fnil_5fnth
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_1
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__assoc_nil_nth.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s 1#u32 (-1) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_a1 h_v1 h_v4 h_v5 v1 v4 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_add s1 e_v7 (by rw [he_v7]; rfl) h_a2 h_v6 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 dropping h_a2 h_v6 he_v7 hinv1 e_v7 s1 v6
  case_again hinv2 hG with h_a0 h_v2 h_v7 in EoCases.__assoc_nil_nth.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's fall-through helpers of `__assoc_nil_nth`, each the program's cases from its first on. -/
theorem eo__24assoc_5fnil_5fnth.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___assoc_nil_nth x_a0 x_a1 x_a2 =
      firstSome [EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___assoc_nil_nth
  unfold EoCases.__assoc_nil_nth.case_1
  logos_eq_deep

/-- logos's `__assoc_nil_nth` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24assoc_5fnil_5fnth.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __assoc_nil_nth x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2, EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __assoc_nil_nth
  unfold EoCases.__assoc_nil_nth.case_0
  have hn := eo__24assoc_5fnil_5fnth.helper_1
  logos_eq_deep

theorem step_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __assoc_nil_nth x_a0 x_a1 x_a2 = __assoc_nil_nth y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24assoc_5fnil_5fnth.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24assoc_5fnil_5fnth
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24assoc_5fnil_5fnth_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24assoc_5fnil_5fnth_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__assoc_nil_nth.case_0 EoCases.__assoc_nil_nth.case_1

theorem body_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24assoc_5fnil_5fnth body_eo__24assoc_5fnil_5fnth_loop
  step with step_eo__24assoc_5fnil_5fnth_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24assoc_5fnil_5fnth at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24assoc_5fnil_5fnth.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24assoc_5fnil_5fnth
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 14#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24assoc_5fnil_5fnth s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_14 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_14 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24assoc_5fnil_5fnth_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24assoc_5fnil_5fnth_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24assoc_5fnil_5fnth_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__assoc_nil_nth_type.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__assoc_nil_nth_type.case_0 x_a0 x_a1 x_a2 = some (__assoc_nil_nth_type y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__assoc_nil_nth_type.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24assoc_5fnil_5fnth_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth_type.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth_type.case_0
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__assoc_nil_nth_type.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a2 h_v5 dropping h_a0 h_a1 h_v1 h_v2 h_v4 v1 v2 v4
  pat_same a2 v6 with h_a2 h_v6 using hinv1 else hinv1 hG in EoCases.__assoc_nil_nth_type.case_0
  store_step with ih.eo__24eo_5ftypeof s1 v5 _ hinv1 h64 (hG.rem hrem) h_v5 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying dropping h_a2 h_v5 h_v6 hinv1 s1 v5 v6
  case_done hinv2 hG with h_v7 in EoCases.__assoc_nil_nth_type.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24assoc_5fnil_5fnth_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24assoc_5fnil_5fnth_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__assoc_nil_nth_type.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__assoc_nil_nth_type.case_1 x_a0 x_a1 x_a2 = some (__assoc_nil_nth_type y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__assoc_nil_nth_type.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24assoc_5fnil_5fnth_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth_type.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth_type.case_1
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__assoc_nil_nth_type.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s 1#u32 (-1) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_a1 h_v1 h_v4 h_v5 v1 v4 v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_add s1 e_v7 (by rw [he_v7]; rfl) h_a2 h_v6 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 dropping h_a2 h_v6 he_v7 hinv1 e_v7 s1 v6
  case_again hinv2 hG with h_a0 h_v2 h_v7 in EoCases.__assoc_nil_nth_type.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's fall-through helpers of `__assoc_nil_nth_type`, each the program's cases from its first on. -/
theorem eo__24assoc_5fnil_5fnth_5ftype.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___assoc_nil_nth_type x_a0 x_a1 x_a2 =
      firstSome [EoCases.__assoc_nil_nth_type.case_1 x_a0 x_a1 x_a2] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___assoc_nil_nth_type
  unfold EoCases.__assoc_nil_nth_type.case_1
  logos_eq_deep

/-- logos's `__assoc_nil_nth_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24assoc_5fnil_5fnth_5ftype.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __assoc_nil_nth_type x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__assoc_nil_nth_type.case_0 x_a0 x_a1 x_a2, EoCases.__assoc_nil_nth_type.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __assoc_nil_nth_type
  unfold EoCases.__assoc_nil_nth_type.case_0
  have hn := eo__24assoc_5fnil_5fnth_5ftype.helper_1
  logos_eq_deep

theorem step_eo__24assoc_5fnil_5fnth_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24assoc_5fnil_5fnth_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__assoc_nil_nth_type x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __assoc_nil_nth_type x_a0 x_a1 x_a2 = __assoc_nil_nth_type y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24assoc_5fnil_5fnth_5ftype.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24assoc_5fnil_5fnth_5ftype
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24assoc_5fnil_5fnth_5ftype_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24assoc_5fnil_5fnth_5ftype_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__assoc_nil_nth_type.case_0 EoCases.__assoc_nil_nth_type.case_1

theorem body_eo__24assoc_5fnil_5fnth_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24assoc_5fnil_5fnth_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth_type x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24assoc_5fnil_5fnth_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth_type x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24assoc_5fnil_5fnth_5ftype body_eo__24assoc_5fnil_5fnth_5ftype_loop
  step with step_eo__24assoc_5fnil_5fnth_5ftype_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24assoc_5fnil_5fnth_5ftype at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24assoc_5fnil_5fnth_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24assoc_5fnil_5fnth_5ftype.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24assoc_5fnil_5fnth_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 15#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24assoc_5fnil_5fnth_5ftype s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__assoc_nil_nth_type x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_15 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_15 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24assoc_5fnil_5fnth_5ftype_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24beta_5freduce_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24beta_5freduce s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__beta_reduce.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__beta_reduce.case_0 x_a0 x_a1 = some (__beta_reduce y0 y1)
      | core.result.Result.Ok none => EoCases.__beta_reduce.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24beta_5freduce
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__beta_reduce.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__beta_reduce.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__beta_reduce.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_lambda.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_a1 h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__beta_reduce.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__beta_reduce.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv1 else hinv1 hG in EoCases.__beta_reduce.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v16 (by rw [he_v16]; exact empty_args) hinv1 h64 as ⟨v16, s2, hinv2, h_v16⟩ growing hG carrying h_a1 h_v2 h_v5 h_v12 h_v14 h_v15 dropping h_v11 h_v7 h_v8 h_v9 he_v16 hinv1 e_v16 s1 v11 v7 v8 v9
  pat_same v14 v16 with h_v14 h_v16 using hinv2 else hinv2 hG in EoCases.__beta_reduce.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v17 (by rw [he_v17]; exact empty_args) hinv2 h64 as ⟨v17, s3, hinv3, h_v17⟩ growing hG carrying h_a1 h_v2 h_v5 h_v12 h_v15 dropping h_v14 h_v16 he_v17 hinv2 e_v17 s2 v14 v16
  pat_same a1 v17 with h_a1 h_v17 using hinv3 else hinv3 hG in EoCases.__beta_reduce.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v18 (by rw [he_v18]; exact empty_args) hinv3 h64 as ⟨v18, s4, hinv4, h_v18⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_a1 h_v17 he_v18 hinv3 e_v18 s3 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s4 e_v19 (by rw [he_v19]; exact empty_args) hinv4 h64 as ⟨v19, s5, hinv5, h_v19⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v18 dropping he_v19 hinv4 e_v19 s4
  store_step with Store.apply_rep s5 v19 v15 _ _ hinv5 h64 h_v19 h_v15 (by ns_tac) (by ns_tac) as ⟨v20, s6, hinv6, h_v20⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v18 dropping h_v19 hinv5 s5 v19
  store_step with Store.apply_rep s6 v20 v12 _ _ hinv6 h64 h_v20 h_v12 (by ns_tac) (by ns_tac) as ⟨v21, s7, hinv7, h_v21⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v18 dropping h_v20 hinv6 s6 v20
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_setof n ih.eo__24eo_5fis_5flist_5fnil s7 e_v22 (by rw [he_v22]; rfl) h_v18 h_v21 hinv7 h64 (hG.rem hrem) (by not_left_tac) as ⟨v22, s8, hinv8, h_v22⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v18 h_v21 he_v22 hinv7 e_v22 s7 v18 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s8 e_v23 (by rw [he_v23]; exact empty_args) hinv8 h64 as ⟨v23, s9, hinv9, h_v23⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v22 dropping he_v23 hinv8 e_v23 s8
  store_step with Store.apply_rep s9 v23 v15 _ _ hinv9 h64 h_v23 h_v15 (by ns_tac) (by ns_tac) as ⟨v24, s10, hinv10, h_v24⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v22 dropping h_v23 hinv9 s9 v23
  store_step with Store.apply_rep s10 v24 v12 _ _ hinv10 h64 h_v24 h_v12 (by ns_tac) (by ns_tac) as ⟨v25, s11, hinv11, h_v25⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v22 dropping h_v24 hinv10 s10 v24
  step as ⟨e_v26, he_v26⟩
  store_step with Store.builtin_spec_eq s11 e_v26 (by rw [he_v26]; rfl) h_v22 h_v25 hinv11 h64 as ⟨v26, s12, hinv12, h_v26⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v22 h_v25 he_v26 hinv11 e_v26 s11 v22 v25
  store_step with Store.literal_boolean_spec s12 true hinv12 h64 as ⟨v27, s13, hinv13, h_v27⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v26 dropping hinv12 s12
  have h_req_v56 := (show requires_2_eo__24beta_5freduce s13 v26 v27 v12 v15 v2 v5 ⦃ r s' => s'.Inv ∧ s13.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_2_eo__24beta_5freduce
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s13
    req_same v26 v27 with h_v26 h_v27 using hinv13 hG
    req_stuck h_v26 as hq_v26 using hinv13 hG
    step as ⟨e_v28, he_v28⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s13 e_v28 (by rw [he_v28]; exact empty_args) hinv13 h64 as ⟨v28, s14, hinv14, h_v28⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v26 h_v27 he_v28 hinv13 e_v28 s13 v26 v27
    step as ⟨e_v29, he_v29⟩
    store_step with Store.builtin_spec_eq s14 e_v29 (by rw [he_v29]; rfl) h_v12 h_v28 hinv14 h64 as ⟨v29, s15, hinv15, h_v29⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v28 he_v29 hinv14 e_v29 s14 v28
    have h_ite_v55 := (show if_1_eo__24beta_5freduce s15 v29 v15 v2 v5 v12 ⦃ r s' => s'.Inv ∧ s15.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold if_1_eo__24beta_5freduce
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s15
      rcases Store.boolean_value_term h_v29 with ⟨hx_30, hbv_30⟩ | ⟨hx_30, hbv_30⟩ | ⟨hx_30, hbv_30⟩
      · ite_branch hbv_30
        store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v30, s16, hinv16, h_v30⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v29 v29
        step as ⟨e_v31, he_v31⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s16 e_v31 (by rw [he_v31]; exact empty_args) hinv16 h64 as ⟨v31, s17, hinv17, h_v31⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 dropping he_v31 e_v31
        store_step with Store.apply_rep s17 v31 v15 _ _ hinv17 h64 h_v31 h_v15 (by ns_tac) (by ns_tac) as ⟨v32, s18, hinv18, h_v32⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 dropping h_v31 v31
        step as ⟨e_v33, he_v33⟩
        store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s18 e_v33 (by rw [he_v33]; exact empty_args) hinv18 h64 as ⟨v33, s19, hinv19, h_v33⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 h_v32 dropping he_v33 e_v33
        store_step with Store.apply_rep s19 v32 v33 _ _ hinv19 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s20, hinv20, h_v34⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 dropping h_v32 h_v33 v32 v33
        step as ⟨e_v35, he_v35⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s20 e_v35 (by rw [he_v35]; exact empty_args) hinv20 h64 as ⟨v35, s21, hinv21, h_v35⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 h_v34 dropping he_v35 e_v35
        store_step with Store.apply_rep s21 v35 v2 _ _ hinv21 h64 h_v35 h_v2 (by ns_tac) (by ns_tac) as ⟨v36, s22, hinv22, h_v36⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 h_v34 dropping h_v35 v35
        step as ⟨e_v37, he_v37⟩
        store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s22 e_v37 (by rw [he_v37]; exact empty_args) hinv22 h64 as ⟨v37, s23, hinv23, h_v37⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 h_v34 h_v36 dropping he_v37 e_v37
        store_step with Store.apply_rep s23 v36 v37 _ _ hinv23 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s24, hinv24, h_v38⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 h_v34 dropping h_v36 h_v37 v36 v37
        step as ⟨e_v39, he_v39⟩
        store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s24 e_v39 (by rw [he_v39]; exact empty_args) hinv24 h64 as ⟨v39, s25, hinv25, h_v39⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v30 h_v34 h_v38 dropping he_v39 e_v39
        store_step with ih.eo__24substitute_5fsimul_5frec s25 v30 v5 v34 v38 v39 _ _ _ _ _ hinv25 h64 (hG.rem hrem) h_v30 h_v5 h_v34 h_v38 h_v39 as ⟨v40, s26, hinv26, h_v40⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v30 h_v34 h_v38 h_v39 v30 v34 v38 v39
        ite_done hinv26 hG with (eo_ite_true_rep _ hx_30 h_v40)
      · ite_branch hbv_30
        store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v41, s16, hinv16, h_v41⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 dropping h_v29 v29
        step as ⟨e_v42, he_v42⟩
        store_step with CtorSpec.eo_lambda.construct s16 e_v42 (by rw [he_v42]; exact empty_args) hinv16 h64 as ⟨v42, s17, hinv17, h_v42⟩ growing hG carrying h_v2 h_v5 h_v12 h_v15 h_v41 dropping he_v42 e_v42
        store_step with Store.apply_rep s17 v42 v12 _ _ hinv17 h64 h_v42 h_v12 (by ns_tac) (by ns_tac) as ⟨v43, s18, hinv18, h_v43⟩ growing hG carrying h_v2 h_v5 h_v15 h_v41 dropping h_v12 h_v42 v12 v42
        store_step with Store.apply_rep s18 v43 v5 _ _ hinv18 h64 h_v43 h_v5 (by ns_tac) (by ns_tac) as ⟨v44, s19, hinv19, h_v44⟩ growing hG carrying h_v2 h_v15 h_v41 dropping h_v43 h_v5 hinv18 s18 v43 v5
        step as ⟨e_v45, he_v45⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s19 e_v45 (by rw [he_v45]; exact empty_args) hinv19 h64 as ⟨v45, s20, hinv20, h_v45⟩ growing hG carrying h_v2 h_v15 h_v41 h_v44 dropping he_v45 hinv19 e_v45 s19
        store_step with Store.apply_rep s20 v45 v15 _ _ hinv20 h64 h_v45 h_v15 (by ns_tac) (by ns_tac) as ⟨v46, s21, hinv21, h_v46⟩ growing hG carrying h_v2 h_v41 h_v44 dropping h_v15 h_v45 hinv20 s20 v15 v45
        step as ⟨e_v47, he_v47⟩
        store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s21 e_v47 (by rw [he_v47]; exact empty_args) hinv21 h64 as ⟨v47, s22, hinv22, h_v47⟩ growing hG carrying h_v2 h_v41 h_v44 h_v46 dropping he_v47 hinv21 e_v47 s21
        store_step with Store.apply_rep s22 v46 v47 _ _ hinv22 h64 h_v46 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s23, hinv23, h_v48⟩ growing hG carrying h_v2 h_v41 h_v44 dropping h_v46 h_v47 hinv22 s22 v46 v47
        step as ⟨e_v49, he_v49⟩
        store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s23 e_v49 (by rw [he_v49]; exact empty_args) hinv23 h64 as ⟨v49, s24, hinv24, h_v49⟩ growing hG carrying h_v2 h_v41 h_v44 h_v48 dropping he_v49 hinv23 e_v49 s23
        store_step with Store.apply_rep s24 v49 v2 _ _ hinv24 h64 h_v49 h_v2 (by ns_tac) (by ns_tac) as ⟨v50, s25, hinv25, h_v50⟩ growing hG carrying h_v41 h_v44 h_v48 dropping h_v2 h_v49 hinv24 s24 v2 v49
        step as ⟨e_v51, he_v51⟩
        store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s25 e_v51 (by rw [he_v51]; exact empty_args) hinv25 h64 as ⟨v51, s26, hinv26, h_v51⟩ growing hG carrying h_v41 h_v44 h_v48 h_v50 dropping he_v51 hinv25 e_v51 s25
        store_step with Store.apply_rep s26 v50 v51 _ _ hinv26 h64 h_v50 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s27, hinv27, h_v52⟩ growing hG carrying h_v41 h_v44 h_v48 dropping h_v50 h_v51 hinv26 s26 v50 v51
        step as ⟨e_v53, he_v53⟩
        store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s27 e_v53 (by rw [he_v53]; exact empty_args) hinv27 h64 as ⟨v53, s28, hinv28, h_v53⟩ growing hG carrying h_v41 h_v44 h_v48 h_v52 dropping he_v53 hinv27 e_v53 s27
        store_step with ih.eo__24substitute_5fsimul_5frec s28 v41 v44 v48 v52 v53 _ _ _ _ _ hinv28 h64 (hG.rem hrem) h_v41 h_v44 h_v48 h_v52 h_v53 as ⟨v54, s29, hinv29, h_v54⟩ growing hG carrying dropping h_v41 h_v44 h_v48 h_v52 h_v53 hinv28 s28 v41 v44 v48 v52 v53
        ite_done hinv29 hG with (eo_ite_false_rep _ hx_30 h_v54)
      · ite_branch hbv_30
        ite_stuck hinv15 hG with hx_30)
    store_step with h_ite_v55 as ⟨v55, s16, hinv16, h_v55⟩ growing hG carrying dropping h_ite_v55 h_v12 h_v15 h_v2 h_v29 h_v5 hinv15 s15 v12 v15 v2 v29 v5
    req_done hinv16 hG with h_v55 using hq_v26)
  store_step with h_req_v56 as ⟨v56, s17, hinv17, h_v56⟩ growing hG carrying dropping h_req_v56 h_v12 h_v15 h_v2 h_v26 h_v27 h_v5 hinv13 s13 v12 v15 v2 v26 v27 v5
  case_done hinv17 hG with h_v56 in EoCases.__beta_reduce.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8 hn_v11 hn_v12 hn_v14 hn_v15

theorem case_1_eo__24beta_5freduce_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24beta_5freduce s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__beta_reduce.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__beta_reduce.case_1 x_a0 x_a1 = some (__beta_reduce y0 y1)
      | core.result.Result.Ok none => EoCases.__beta_reduce.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24beta_5freduce
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__beta_reduce.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__beta_reduce.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_lambda.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__beta_reduce.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a1 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_list_setof n ih.eo__24eo_5fis_5flist_5fnil s2 e_v8 (by rw [he_v8]; rfl) h_v7 h_v5 hinv2 h64 (hG.rem hrem) (by not_left_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a1 h_v2 h_v5 dropping h_v7 he_v8 hinv2 e_v8 s2 v7
  step as ⟨e_v9, he_v9⟩
  store_step with Store.builtin_spec_eq s3 e_v9 (by rw [he_v9]; rfl) h_v8 h_v5 hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a1 h_v2 h_v5 dropping h_v8 he_v9 hinv3 e_v9 s3 v8
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a1 h_v2 h_v5 h_v9 dropping hinv4 s4
  have h_req_v14 := (show requires_4_eo__24beta_5freduce s5 v9 v10 v2 v5 a1 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_4_eo__24beta_5freduce
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v9 v10 with h_v9 h_v10 using hinv5 hG
    req_stuck h_v9 as hq_v9 using hinv5 hG
    store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a1 h_v2 h_v5 dropping h_v10 h_v9 hinv5 s5 v10 v9
    step as ⟨e_v12, he_v12⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a1 h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
    store_step with ih.eo__24substitute_5fsimul_5frec s7 v11 v2 v5 a1 v12 _ _ _ _ _ hinv7 h64 (hG.rem hrem) h_v11 h_v2 h_v5 h_a1 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying dropping h_a1 h_v11 h_v12 h_v2 h_v5 hinv7 s7 v11 v12 v2 v5
    req_done hinv8 hG with h_v13 using hq_v9)
  store_step with h_req_v14 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying dropping h_req_v14 h_v10 h_v2 h_v5 h_v9 hinv5 s5 v10 v2 v5 v9
  case_done hinv9 hG with h_v14 in EoCases.__beta_reduce.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_2_eo__24beta_5freduce_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24beta_5freduce s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__beta_reduce.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          EoCases.__beta_reduce.case_2 x_a0 x_a1 = some (__beta_reduce y0 y1)
      | core.result.Result.Ok none => EoCases.__beta_reduce.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24beta_5freduce
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__beta_reduce.case_2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  store_step with Store.apply_rep s1 v3 v2 _ _ hinv1 h64 h_v3 h_v2 (by ns_tac) (by ns_tac) as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 h_v1 dropping h_v2 h_v3 hinv1 s1 v2 v3
  store_step with Store.apply_rep s2 v4 a1 _ _ hinv2 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v1 dropping h_a1 h_v4 hinv2 s2 v4
  case_again hinv3 hG with h_v1 h_v5 in EoCases.__beta_reduce.case_2 using hn_a0 hn_a1 hn_v1 hn_v2

/-- logos's `__beta_reduce` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24beta_5freduce.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __beta_reduce x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__beta_reduce.case_0 x_a0 x_a1, EoCases.__beta_reduce.case_1 x_a0 x_a1, EoCases.__beta_reduce.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __beta_reduce
  unfold EoCases.__beta_reduce.case_0 EoCases.__beta_reduce.case_1 EoCases.__beta_reduce.case_2
  logos_eq

theorem step_eo__24beta_5freduce_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    step_eo__24beta_5freduce s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__beta_reduce x_a0 x_a1)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _), arr.val = [u0, u1] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧
          __beta_reduce x_a0 x_a1 = __beta_reduce y0 y1
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24beta_5freduce.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold step_eo__24beta_5freduce
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  round_step with case_0_eo__24beta_5freduce_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1
  round_step with case_1_eo__24beta_5freduce_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0
  round_step with case_2_eo__24beta_5freduce_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 hbud using hn_a0 hn_a1 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__beta_reduce.case_0 EoCases.__beta_reduce.case_1 EoCases.__beta_reduce.case_2

theorem body_eo__24beta_5freduce_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24beta_5freduce s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__beta_reduce x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 : Term) (s : Store) (x_a0 : _) (x_a1 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
      body_eo__24beta_5freduce s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__beta_reduce x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 s x_a0 x_a1 le_rfl hinv hrem h_a0 h_a1
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 s x_a0 x_a1 hk hinv hrem h_a0 h_a1
  unfold body_eo__24beta_5freduce body_eo__24beta_5freduce_loop
  step with step_eo__24beta_5freduce_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24beta_5freduce at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24beta_5freduce_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24beta_5freduce.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24beta_5freduce
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 16#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24beta_5freduce s1 a0 a1) (fun s' t => Represents.rep s' t (__beta_reduce x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_16 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_16 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24beta_5freduce_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_binary.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_binary.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fapply_5fbinary
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a1 h_a2 dropping
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a2 dropping h_a1 h_v0 hinv1 s1 v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_binary.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a2 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_bitblast_apply_binary.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_binary.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_binary.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fapply_5fbinary
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_binary.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_binary.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_1
  pat_unapply h_a2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_binary.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  store_step with ih.eo__24bv_5fbitblast_5fbinary_5fapp s3 a0 v5 v12 _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v5 h_v12 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v2 h_v9 h_v14 dropping h_v12 h_v5 hinv3 s3 v12 v5
  store_step with Store.apply_mk_rep s4 v14 v15 _ _ hinv4 h64 h_v14 h_v15 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v2 h_v9 dropping h_v14 h_v15 hinv4 s4 v14 v15
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fbinary s5 a0 v2 v9 _ _ _ hinv5 h64 (hG.rem hrem) h_a0 h_v2 h_v9 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v16 dropping h_a0 h_v2 h_v9 hinv5 s5 v2 v9
  store_step with Store.apply_mk_rep s6 v16 v17 _ _ hinv6 h64 h_v16 h_v17 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying dropping h_v16 h_v17 hinv6 s6 v16 v17
  case_done hinv7 hG with h_v18 in EoCases.__bv_bitblast_apply_binary.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_apply_binary` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fapply_5fbinary.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_apply_binary x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_apply_binary.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_apply_binary.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_apply_binary
  unfold EoCases.__bv_bitblast_apply_binary.case_0 EoCases.__bv_bitblast_apply_binary.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_binary x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fapply_5fbinary.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fapply_5fbinary
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fapply_5fbinary_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fapply_5fbinary_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_apply_binary.case_0 EoCases.__bv_bitblast_apply_binary.case_1

theorem eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fapply_5fbinary.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fapply_5fbinary
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 17#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fapply_5fbinary s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_apply_binary x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_17 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_17 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fapply_5fbinary_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_ite.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_ite.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fapply_5fite
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a1 h_a2 dropping
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a2 dropping h_a1 h_v0 hinv1 s1 v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_ite.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a2 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_bitblast_apply_ite.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_ite.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_ite.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fapply_5fite
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_ite.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_ite.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_1
  pat_unapply h_a2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a2 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_ite.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v12 h_v14 dropping he_v15 hinv3 e_v15 s3
  store_step with Store.apply_rep s4 v15 a0 _ _ hinv4 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_v2 h_v5 h_v9 h_v12 h_v14 dropping h_v15 hinv4 s4 v15
  store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_v2 h_v9 h_v12 h_v14 dropping h_v16 h_v5 hinv5 s5 v16 v5
  store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_v2 h_v9 h_v14 dropping h_v12 h_v17 hinv6 s6 v12 v17
  store_step with Store.apply_rep s7 v14 v18 _ _ hinv7 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_v2 h_v9 dropping h_v14 h_v18 hinv7 s7 v14 v18
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fite s8 a0 v2 v9 _ _ _ hinv8 h64 (hG.rem hrem) h_a0 h_v2 h_v9 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v19 dropping h_a0 h_v2 h_v9 hinv8 s8 v2 v9
  store_step with Store.apply_mk_rep s9 v19 v20 _ _ hinv9 h64 h_v19 h_v20 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying dropping h_v19 h_v20 hinv9 s9 v19 v20
  case_done hinv10 hG with h_v21 in EoCases.__bv_bitblast_apply_ite.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_apply_ite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fapply_5fite.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_apply_ite x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_apply_ite.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_apply_ite.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_apply_ite
  unfold EoCases.__bv_bitblast_apply_ite.case_0 EoCases.__bv_bitblast_apply_ite.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fapply_5fite.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fapply_5fite
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fapply_5fite_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fapply_5fite_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_apply_ite.case_0 EoCases.__bv_bitblast_apply_ite.case_1

theorem eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fapply_5fite.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fapply_5fite
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 18#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fapply_5fite s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_apply_ite x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_18 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_18 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fapply_5fite_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_unary.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_unary.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fapply_5funary
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a1 dropping
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_unary.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a1 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_apply_unary.case_0 using hn_a0 hn_a1

theorem case_1_eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_unary.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_unary.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fapply_5funary
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_unary.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_unary.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_unary.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  store_step with Store.apply_rep s2 a0 v5 _ _ hinv2 h64 h_a0 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 h_v7 dropping h_v5 hinv2 s2 v5
  store_step with Store.apply_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 dropping h_v7 h_v8 hinv3 s3 v7 v8
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s4 a0 v2 _ _ hinv4 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v9 dropping h_a0 h_v2 hinv4 s4 v2
  store_step with Store.apply_mk_rep s5 v9 v10 _ _ hinv5 h64 h_v9 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying dropping h_v10 h_v9 hinv5 s5 v10 v9
  case_done hinv6 hG with h_v11 in EoCases.__bv_bitblast_apply_unary.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_apply_unary` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fapply_5funary.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_bitblast_apply_unary x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_apply_unary.case_0 x_a0 x_a1, EoCases.__bv_bitblast_apply_unary.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_apply_unary
  unfold EoCases.__bv_bitblast_apply_unary.case_0 EoCases.__bv_bitblast_apply_unary.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_unary x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fapply_5funary.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fbitblast_5fapply_5funary
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fapply_5funary_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fbitblast_5fapply_5funary_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_bitblast_apply_unary.case_0 EoCases.__bv_bitblast_apply_unary.case_1

theorem eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fapply_5funary.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fbitblast_5fapply_5funary
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 19#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fapply_5funary s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_bitblast_apply_unary x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_19 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_19 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fapply_5funary_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
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
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_and.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_and.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a2 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v2 dropping h_a2 h_v3 hinv4 s4 v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v2 h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v2 dropping h_v4 h_v5 hinv6 s6 v4 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_v2 h_v6 hinv7 s7 v2 v6
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
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_or.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_or.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a2 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_v2 dropping h_a2 h_v3 hinv4 s4 v3
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v2 h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_v2 dropping h_v4 h_v5 hinv6 s6 v4 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_v2 h_v6 hinv7 s7 v2 v6
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
  store_step with CtorSpec.eo_xor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
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

theorem case_0_eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_concat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_concat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fconcat
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_concat.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_concat.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_concat.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a1 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a1 h_v2 dropping h_v5 h_v7 hinv2 s2 v5 v7
  store_step with ih.eo__24bv_5fbitblast_5fconcat s3 v2 a1 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v8 dropping h_a1 h_v2 hinv3 s3 v2
  store_step with Store.apply_mk_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying dropping h_v8 h_v9 hinv4 s4 v8 v9
  case_done hinv5 hG with h_v10 in EoCases.__bv_bitblast_concat.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_concat.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_concat.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fconcat
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_concat.case_1
  case_done hinv1 hG with h_a1 in EoCases.__bv_bitblast_concat.case_1 using hn_a0 hn_a1

/-- logos's `__bv_bitblast_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fconcat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_bitblast_concat x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_concat.case_0 x_a0 x_a1, EoCases.__bv_bitblast_concat.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_concat
  unfold EoCases.__bv_bitblast_concat.case_0 EoCases.__bv_bitblast_concat.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fconcat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fbitblast_5fconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fconcat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fbitblast_5fconcat_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_bitblast_concat.case_0 EoCases.__bv_bitblast_concat.case_1

theorem eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fconcat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fbitblast_5fconcat
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 21#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fconcat s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_bitblast_concat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_21 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_21 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fconcat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
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
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v4 h_v5 dropping h_a0 h_v1 h_v2 he_v6 e_v6 v1 v2
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

theorem case_0_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_prefix.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_prefix.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_prefix.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_prefix.case_0 using hn_a0 hn_a1

theorem case_1_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_prefix.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_prefix.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a1 dropping
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_prefix.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a1 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_prefix.case_1 using hn_a0 hn_a1

theorem case_2_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_prefix.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_prefix.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_prefix.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_prefix.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_prefix.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v2 dropping h_v5 h_v7 hinv2 s2 v5 v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s3 1#u32 (-1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v2 h_v8 dropping hinv3 s3
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_add s4 e_v10 (by rw [he_v10]; rfl) h_a0 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v8 dropping h_a0 h_v9 he_v10 hinv4 e_v10 s4 v9
  store_step with ih.eo__24bv_5fbitblast_5fprefix s5 v10 v2 _ _ hinv5 h64 (hG.rem hrem) h_v10 h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v8 dropping h_v10 h_v2 hinv5 s5 v10 v2
  store_step with Store.apply_mk_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying dropping h_v11 h_v8 hinv6 s6 v11 v8
  case_done hinv7 hG with h_v12 in EoCases.__bv_bitblast_prefix.case_2 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_prefix` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fprefix.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_bitblast_prefix x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_prefix.case_0 x_a0 x_a1, EoCases.__bv_bitblast_prefix.case_1 x_a0 x_a1, EoCases.__bv_bitblast_prefix.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_prefix
  unfold EoCases.__bv_bitblast_prefix.case_0 EoCases.__bv_bitblast_prefix.case_1 EoCases.__bv_bitblast_prefix.case_2
  logos_eq

theorem body_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_prefix x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fprefix.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fprefix_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fbitblast_5fprefix_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  case_step with case_2_eo__24bv_5fbitblast_5fprefix_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__bv_bitblast_prefix.case_0 EoCases.__bv_bitblast_prefix.case_1 EoCases.__bv_bitblast_prefix.case_2

theorem eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fprefix.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fbitblast_5fprefix
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 23#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fprefix s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_bitblast_prefix x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_23 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_23 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fprefix_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fslt_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fslt_5fimpl s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_slt_impl.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_slt_impl.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fslt_5fimpl
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_slt_impl.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_slt_impl.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_slt_impl.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a1 h_a2 h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  pat_same v2 v7 with h_v2 h_v7 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_slt_impl.case_0
  pat_unapply h_a1 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__bv_bitblast_slt_impl.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__bv_bitblast_slt_impl.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a2 h_v5 h_v10 h_v12 h_v13 dropping h_a1 h_v2 h_v7 h_v9 he_v14 hinv2 e_v14 s2 v2 v7 v9
  pat_same v12 v14 with h_v12 h_v14 using hinv3 else hinv3 hG in EoCases.__bv_bitblast_slt_impl.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s3 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a2 h_v5 h_v10 h_v13 dropping h_v12 h_v14 hinv3 s3 v12 v14
  pat_same v10 v15 with h_v10 h_v15 using hinv4 else hinv4 hG in EoCases.__bv_bitblast_slt_impl.case_0
  have h_ite_v44 := (show if_1_eo__24bv_5fbitblast_5fslt_5fimpl s4 a2 v5 v13 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24bv_5fbitblast_5fslt_5fimpl
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_a2 with ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩ | ⟨hx_16, hbv_16⟩
    · ite_branch hbv_16
      step as ⟨e_v16, he_v16⟩
      store_step with CtorSpec.eo_or.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v5 h_v13 dropping h_a2 h_v10 h_v15 he_v16 e_v16 v10 v15
      step as ⟨e_v17, he_v17⟩
      store_step with CtorSpec.eo__3d.construct s5 e_v17 (by rw [he_v17]; exact empty_args) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v5 h_v13 h_v16 dropping he_v17 e_v17
      store_step with Store.apply_rep s6 v17 v5 _ _ hinv6 h64 h_v17 h_v5 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v5 h_v13 h_v16 dropping h_v17 v17
      store_step with Store.apply_rep s7 v18 v13 _ _ hinv7 h64 h_v18 h_v13 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v5 h_v13 h_v16 dropping h_v18 v18
      store_step with Store.apply_rep s8 v16 v19 _ _ hinv8 h64 h_v16 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v5 h_v13 dropping h_v16 h_v19 v16 v19
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo_or.construct s9 e_v21 (by rw [he_v21]; exact empty_args) hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v5 h_v13 h_v20 dropping he_v21 e_v21
      step as ⟨e_v22, he_v22⟩
      store_step with CtorSpec.eo_and.construct s10 e_v22 (by rw [he_v22]; exact empty_args) hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 dropping he_v22 e_v22
      store_step with Store.apply_rep s11 v22 v5 _ _ hinv11 h64 h_v22 h_v5 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 dropping h_v22 v22
      step as ⟨e_v24, he_v24⟩
      store_step with CtorSpec.eo_and.construct s12 e_v24 (by rw [he_v24]; exact empty_args) hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 h_v23 dropping he_v24 e_v24
      step as ⟨e_v25, he_v25⟩
      store_step with CtorSpec.eo_not.construct s13 e_v25 (by rw [he_v25]; exact empty_args) hinv13 h64 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 h_v23 h_v24 dropping he_v25 e_v25
      store_step with Store.apply_rep s14 v25 v13 _ _ hinv14 h64 h_v25 h_v13 (by ns_tac) (by ns_tac) as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 h_v23 h_v24 dropping h_v25 hinv14 s14 v25
      store_step with Store.apply_rep s15 v24 v26 _ _ hinv15 h64 h_v24 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 h_v23 dropping h_v24 h_v26 hinv15 s15 v24 v26
      store_step with Store.literal_boolean_spec s16 true hinv16 h64 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 h_v23 h_v27 dropping hinv16 s16
      store_step with Store.apply_rep s17 v27 v28 _ _ hinv17 h64 h_v27 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 h_v23 dropping h_v27 h_v28 hinv17 s17 v27 v28
      store_step with Store.apply_rep s18 v23 v29 _ _ hinv18 h64 h_v23 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_v5 h_v13 h_v20 h_v21 dropping h_v23 h_v29 hinv18 s18 v23 v29
      store_step with Store.apply_rep s19 v21 v30 _ _ hinv19 h64 h_v21 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_v5 h_v13 h_v20 dropping h_v21 h_v30 hinv19 s19 v21 v30
      store_step with Store.literal_boolean_spec s20 false hinv20 h64 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_v5 h_v13 h_v20 h_v31 dropping hinv20 s20
      store_step with Store.apply_rep s21 v31 v32 _ _ hinv21 h64 h_v31 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_v5 h_v13 h_v20 dropping h_v31 h_v32 hinv21 s21 v31 v32
      store_step with Store.apply_rep s22 v20 v33 _ _ hinv22 h64 h_v20 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_v5 h_v13 dropping h_v20 h_v33 hinv22 s22 v20 v33
      ite_done hinv23 hG with (eo_ite_true_rep _ hx_16 h_v34)
    · ite_branch hbv_16
      step as ⟨e_v35, he_v35⟩
      store_step with CtorSpec.eo_and.construct s4 e_v35 (by rw [he_v35]; exact empty_args) hinv4 h64 as ⟨v35, s5, hinv5, h_v35⟩ growing hG carrying h_v5 h_v13 dropping h_a2 h_v10 h_v15 he_v35 e_v35 v10 v15
      store_step with Store.apply_rep s5 v35 v5 _ _ hinv5 h64 h_v35 h_v5 (by ns_tac) (by ns_tac) as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_v13 dropping h_v35 h_v5 v35 v5
      step as ⟨e_v37, he_v37⟩
      store_step with CtorSpec.eo_and.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_v13 h_v36 dropping he_v37 hinv6 e_v37 s6
      step as ⟨e_v38, he_v38⟩
      store_step with CtorSpec.eo_not.construct s7 e_v38 (by rw [he_v38]; exact empty_args) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_v13 h_v36 h_v37 dropping he_v38 hinv7 e_v38 s7
      store_step with Store.apply_rep s8 v38 v13 _ _ hinv8 h64 h_v38 h_v13 (by ns_tac) (by ns_tac) as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_v36 h_v37 dropping h_v13 h_v38 hinv8 s8 v13 v38
      store_step with Store.apply_rep s9 v37 v39 _ _ hinv9 h64 h_v37 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_v36 dropping h_v37 h_v39 hinv9 s9 v37 v39
      store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_v36 h_v40 dropping hinv10 s10
      store_step with Store.apply_rep s11 v40 v41 _ _ hinv11 h64 h_v40 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_v36 dropping h_v40 h_v41 hinv11 s11 v40 v41
      store_step with Store.apply_rep s12 v36 v42 _ _ hinv12 h64 h_v36 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying dropping h_v36 h_v42 hinv12 s12 v36 v42
      ite_done hinv13 hG with (eo_ite_false_rep _ hx_16 h_v43)
    · ite_branch hbv_16
      ite_stuck hinv4 hG with hx_16)
  store_step with h_ite_v44 as ⟨v44, s5, hinv5, h_v44⟩ growing hG carrying dropping h_ite_v44 h_v10 h_v13 h_v15 h_v5 hinv4 s4 v10 v13 v15 v5
  case_done hinv5 hG with h_v44 in EoCases.__bv_bitblast_slt_impl.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_1_eo__24bv_5fbitblast_5fslt_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fslt_5fimpl s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_slt_impl.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_slt_impl.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fslt_5fimpl
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_slt_impl.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_slt_impl.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_slt_impl.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_slt_impl.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_slt_impl.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a1 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_slt_impl.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_and.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 dropping he_v15 hinv3 e_v15 s3
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping he_v16 hinv4 e_v16 s4
  store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping h_v16 hinv5 s5 v16
  store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping h_v17 hinv6 s6 v17
  store_step with Store.apply_rep s7 v15 v18 _ _ hinv7 h64 h_v15 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 dropping h_v15 h_v18 hinv7 s7 v15 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_and.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v19 dropping he_v20 hinv8 e_v20 s8
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s9 e_v21 (by rw [he_v21]; exact empty_args) hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v19 h_v20 dropping he_v21 hinv9 e_v21 s9
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s10 e_v22 (by rw [he_v22]; rfl) h_v21 h_v2 hinv10 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a2 h_v5 h_v9 h_v12 h_v14 h_v19 h_v20 dropping h_v2 h_v21 he_v22 hinv10 e_v22 s10 v2 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s11 e_v23 (by rw [he_v23]; exact empty_args) hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a2 h_v5 h_v9 h_v12 h_v14 h_v19 h_v20 h_v22 dropping he_v23 hinv11 e_v23 s11
  step as ⟨e_v24, he_v24⟩
  store_step with Store.builtin_spec_list_rev n ih.eo__24eo_5fis_5flist_5fnil s12 e_v24 (by rw [he_v24]; rfl) h_v23 h_v9 hinv12 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a2 h_v5 h_v12 h_v14 h_v19 h_v20 h_v22 dropping h_v23 h_v9 he_v24 hinv12 e_v24 s12 v23 v9
  store_step with ih.eo__24bv_5fbitblast_5fult s13 v22 v24 a2 _ _ _ hinv13 h64 (hG.rem hrem) h_v22 h_v24 h_a2 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v5 h_v12 h_v14 h_v19 h_v20 dropping h_a2 h_v22 h_v24 hinv13 s13 v22 v24
  store_step with Store.apply_mk_rep s14 v20 v25 _ _ hinv14 h64 h_v20 h_v25 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v5 h_v12 h_v14 h_v19 dropping h_v20 h_v25 hinv14 s14 v20 v25
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v5 h_v12 h_v14 h_v19 h_v26 dropping hinv15 s15
  store_step with Store.apply_mk_rep s16 v26 v27 _ _ hinv16 h64 h_v26 h_v27 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v5 h_v12 h_v14 h_v19 dropping h_v26 h_v27 hinv16 s16 v26 v27
  store_step with Store.apply_mk_rep s17 v19 v28 _ _ hinv17 h64 h_v19 h_v28 as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_v5 h_v12 h_v14 dropping h_v19 h_v28 hinv17 s17 v19 v28
  store_step with Store.apply_mk_rep s18 v14 v29 _ _ hinv18 h64 h_v14 h_v29 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_v5 h_v12 dropping h_v14 h_v29 hinv18 s18 v14 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_or.construct s19 e_v31 (by rw [he_v31]; exact empty_args) hinv19 h64 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_v5 h_v12 h_v30 dropping he_v31 hinv19 e_v31 s19
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_and.construct s20 e_v32 (by rw [he_v32]; exact empty_args) hinv20 h64 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_v5 h_v12 h_v30 h_v31 dropping he_v32 hinv20 e_v32 s20
  store_step with Store.apply_rep s21 v32 v5 _ _ hinv21 h64 h_v32 h_v5 (by ns_tac) (by ns_tac) as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_v12 h_v30 h_v31 dropping h_v32 h_v5 hinv21 s21 v32 v5
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_and.construct s22 e_v34 (by rw [he_v34]; exact empty_args) hinv22 h64 as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_v12 h_v30 h_v31 h_v33 dropping he_v34 hinv22 e_v34 s22
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_not.construct s23 e_v35 (by rw [he_v35]; exact empty_args) hinv23 h64 as ⟨v35, s24, hinv24, h_v35⟩ growing hG carrying h_v12 h_v30 h_v31 h_v33 h_v34 dropping he_v35 hinv23 e_v35 s23
  store_step with Store.apply_rep s24 v35 v12 _ _ hinv24 h64 h_v35 h_v12 (by ns_tac) (by ns_tac) as ⟨v36, s25, hinv25, h_v36⟩ growing hG carrying h_v30 h_v31 h_v33 h_v34 dropping h_v12 h_v35 hinv24 s24 v12 v35
  store_step with Store.apply_rep s25 v34 v36 _ _ hinv25 h64 h_v34 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s26, hinv26, h_v37⟩ growing hG carrying h_v30 h_v31 h_v33 dropping h_v34 h_v36 hinv25 s25 v34 v36
  store_step with Store.literal_boolean_spec s26 true hinv26 h64 as ⟨v38, s27, hinv27, h_v38⟩ growing hG carrying h_v30 h_v31 h_v33 h_v37 dropping hinv26 s26
  store_step with Store.apply_rep s27 v37 v38 _ _ hinv27 h64 h_v37 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s28, hinv28, h_v39⟩ growing hG carrying h_v30 h_v31 h_v33 dropping h_v37 h_v38 hinv27 s27 v37 v38
  store_step with Store.apply_rep s28 v33 v39 _ _ hinv28 h64 h_v33 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s29, hinv29, h_v40⟩ growing hG carrying h_v30 h_v31 dropping h_v33 h_v39 hinv28 s28 v33 v39
  store_step with Store.apply_rep s29 v31 v40 _ _ hinv29 h64 h_v31 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s30, hinv30, h_v41⟩ growing hG carrying h_v30 dropping h_v31 h_v40 hinv29 s29 v31 v40
  store_step with Store.literal_boolean_spec s30 false hinv30 h64 as ⟨v42, s31, hinv31, h_v42⟩ growing hG carrying h_v30 h_v41 dropping hinv30 s30
  store_step with Store.apply_rep s31 v41 v42 _ _ hinv31 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s32, hinv32, h_v43⟩ growing hG carrying h_v30 dropping h_v41 h_v42 hinv31 s31 v41 v42
  store_step with Store.apply_mk_rep s32 v30 v43 _ _ hinv32 h64 h_v30 h_v43 as ⟨v44, s33, hinv33, h_v44⟩ growing hG carrying dropping h_v30 h_v43 hinv32 s32 v30 v43
  case_done hinv33 hG with h_v44 in EoCases.__bv_bitblast_slt_impl.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_slt_impl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fslt_5fimpl.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_slt_impl x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_slt_impl.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_slt_impl.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_slt_impl
  unfold EoCases.__bv_bitblast_slt_impl.case_0 EoCases.__bv_bitblast_slt_impl.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fslt_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fslt_5fimpl s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_slt_impl x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fslt_5fimpl.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fslt_5fimpl
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fslt_5fimpl_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fslt_5fimpl_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_slt_impl.case_0 EoCases.__bv_bitblast_slt_impl.case_1

theorem eo__24bv_5fbitblast_5fslt_5fimpl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fslt_5fimpl.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fslt_5fimpl
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fslt_5fimpl s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_slt_impl x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fslt_5fimpl_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2 = some (__bv_bitblast_subsequence y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a2 dropping
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_subsequence.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a2 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_subsequence.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2 = some (__bv_bitblast_subsequence y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_subsequence.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 hinv1 s1 v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_add s2 e_v2 (by rw [he_v2]; rfl) h_a1 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 he_v2 hinv2 e_v2 s2 v1
  store_step with ih.eo__24bv_5fbitblast_5fprefix s3 v2 a2 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a2 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__bv_bitblast_subsequence.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2 = some (__bv_bitblast_subsequence y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_subsequence.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_subsequence.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v2 h_v4 dropping h_a2 h_v1 h_v5 he_v6 e_v6 v1 v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_subsequence.case_2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s1 1#u32 (-1) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v2 dropping h_v4 h_v6 hinv1 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_add s2 e_v8 (by rw [he_v8]; rfl) h_a0 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a1 h_v2 dropping h_a0 h_v7 he_v8 hinv2 e_v8 s2 v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s3 1#u32 (-1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a1 h_v2 h_v8 dropping hinv3 s3
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_add s4 e_v10 (by rw [he_v10]; rfl) h_a1 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v8 dropping h_a1 h_v9 he_v10 hinv4 e_v10 s4 v9
  case_again hinv5 hG with h_v8 h_v10 h_v2 in EoCases.__bv_bitblast_subsequence.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_subsequence` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fsubsequence.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_subsequence x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_subsequence
  unfold EoCases.__bv_bitblast_subsequence.case_0 EoCases.__bv_bitblast_subsequence.case_1 EoCases.__bv_bitblast_subsequence.case_2
  logos_eq

theorem step_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __bv_bitblast_subsequence x_a0 x_a1 x_a2 = __bv_bitblast_subsequence y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fsubsequence.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24bv_5fbitblast_5fsubsequence_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24bv_5fbitblast_5fsubsequence_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_step with case_2_eo__24bv_5fbitblast_5fsubsequence_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 in EoCases.__bv_bitblast_subsequence.case_0 EoCases.__bv_bitblast_subsequence.case_1 EoCases.__bv_bitblast_subsequence.case_2

theorem body_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24bv_5fbitblast_5fsubsequence body_eo__24bv_5fbitblast_5fsubsequence_loop
  step with step_eo__24bv_5fbitblast_5fsubsequence_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24bv_5fbitblast_5fsubsequence at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fsubsequence.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fsubsequence
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 25#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fsubsequence s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_25 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_25 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fsubsequence_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
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
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_a0 h_v1 h_v5 he_v6 e_v6 v1 v5
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

theorem case_0_eo__24bv_5fbitblast_5fult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fult s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_ult.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_ult.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fult
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a1 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_ult.case_0
  have h_ite_v42 := (show if_1_eo__24bv_5fbitblast_5fult s2 a2 v5 v12 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24bv_5fbitblast_5fult
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_a2 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
    · ite_branch hbv_14
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo_or.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 dropping h_a2 h_v11 h_v13 he_v14 e_v14 v11 v13
      step as ⟨e_v15, he_v15⟩
      store_step with CtorSpec.eo_and.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 dropping he_v15 e_v15
      step as ⟨e_v16, he_v16⟩
      store_step with CtorSpec.eo_not.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping he_v16 e_v16
      store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping h_v16 v16
      store_step with Store.apply_rep s6 v15 v17 _ _ hinv6 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 dropping h_v15 h_v17 v15 v17
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo_and.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v18 dropping he_v19 e_v19
      store_step with Store.apply_rep s8 v19 v12 _ _ hinv8 h64 h_v19 h_v12 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v18 dropping h_v19 v19
      store_step with Store.literal_boolean_spec s9 true hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v18 h_v20 dropping
      store_step with Store.apply_rep s10 v20 v21 _ _ hinv10 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v18 dropping h_v20 h_v21 v20 v21
      store_step with Store.apply_rep s11 v18 v22 _ _ hinv11 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 dropping h_v18 h_v22 v18 v22
      store_step with Store.apply_rep s12 v14 v23 _ _ hinv12 h64 h_v14 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 dropping h_v14 h_v23 hinv12 s12 v14 v23
      step as ⟨e_v25, he_v25⟩
      store_step with CtorSpec.eo_or.construct s13 e_v25 (by rw [he_v25]; exact empty_args) hinv13 h64 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 dropping he_v25 hinv13 e_v25 s13
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo__3d.construct s14 e_v26 (by rw [he_v26]; exact empty_args) hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 h_v25 dropping he_v26 hinv14 e_v26 s14
      store_step with Store.apply_rep s15 v26 v5 _ _ hinv15 h64 h_v26 h_v5 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 h_v25 dropping h_v26 hinv15 s15 v26
      store_step with Store.apply_rep s16 v27 v12 _ _ hinv16 h64 h_v27 h_v12 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 h_v25 dropping h_v27 hinv16 s16 v27
      store_step with Store.apply_rep s17 v25 v28 _ _ hinv17 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 dropping h_v25 h_v28 hinv17 s17 v25 v28
      store_step with Store.literal_boolean_spec s18 false hinv18 h64 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 h_v29 dropping hinv18 s18
      store_step with Store.apply_rep s19 v29 v30 _ _ hinv19 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v24 dropping h_v29 h_v30 hinv19 s19 v29 v30
      store_step with Store.apply_rep s20 v24 v31 _ _ hinv20 h64 h_v24 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 dropping h_v24 h_v31 hinv20 s20 v24 v31
      ite_done hinv21 hG with (eo_ite_true_rep _ hx_14 h_v32)
    · ite_branch hbv_14
      step as ⟨e_v33, he_v33⟩
      store_step with CtorSpec.eo_and.construct s2 e_v33 (by rw [he_v33]; exact empty_args) hinv2 h64 as ⟨v33, s3, hinv3, h_v33⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 dropping h_a2 h_v11 h_v13 he_v33 e_v33 v11 v13
      step as ⟨e_v34, he_v34⟩
      store_step with CtorSpec.eo_not.construct s3 e_v34 (by rw [he_v34]; exact empty_args) hinv3 h64 as ⟨v34, s4, hinv4, h_v34⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v33 dropping he_v34 e_v34
      store_step with Store.apply_rep s4 v34 v5 _ _ hinv4 h64 h_v34 h_v5 (by ns_tac) (by ns_tac) as ⟨v35, s5, hinv5, h_v35⟩ growing hG carrying h_v2 h_v9 h_v12 h_v33 dropping h_v34 h_v5 v34 v5
      store_step with Store.apply_rep s5 v33 v35 _ _ hinv5 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v33 h_v35 hinv5 s5 v33 v35
      step as ⟨e_v37, he_v37⟩
      store_step with CtorSpec.eo_and.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_v2 h_v9 h_v12 h_v36 dropping he_v37 hinv6 e_v37 s6
      store_step with Store.apply_rep s7 v37 v12 _ _ hinv7 h64 h_v37 h_v12 (by ns_tac) (by ns_tac) as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_v2 h_v9 h_v36 dropping h_v12 h_v37 hinv7 s7 v12 v37
      store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_v2 h_v9 h_v36 h_v38 dropping hinv8 s8
      store_step with Store.apply_rep s9 v38 v39 _ _ hinv9 h64 h_v38 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_v2 h_v9 h_v36 dropping h_v38 h_v39 hinv9 s9 v38 v39
      store_step with Store.apply_rep s10 v36 v40 _ _ hinv10 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_v2 h_v9 dropping h_v36 h_v40 hinv10 s10 v36 v40
      ite_done hinv11 hG with (eo_ite_false_rep _ hx_14 h_v41)
    · ite_branch hbv_14
      ite_stuck hinv2 hG with hx_14)
  store_step with h_ite_v42 as ⟨v42, s3, hinv3, h_v42⟩ growing hG carrying h_v2 h_v9 dropping h_ite_v42 h_v11 h_v12 h_v13 h_v5 hinv2 s2 v11 v12 v13 v5
  store_step with ih.eo__24bv_5fbitblast_5fult_5frec s3 v2 v9 v42 _ _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v9 h_v42 as ⟨v43, s4, hinv4, h_v43⟩ growing hG carrying dropping h_v2 h_v42 h_v9 hinv3 s3 v2 v42 v9
  case_done hinv4 hG with h_v43 in EoCases.__bv_bitblast_ult.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_ult` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fult.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_ult x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_ult.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_ult
  unfold EoCases.__bv_bitblast_ult.case_0
  logos_eq

theorem body_eo__24bv_5fbitblast_5fult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fult s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fult.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fult_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__bv_bitblast_ult.case_0

theorem eo__24bv_5fbitblast_5fult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fult.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fult s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_ult x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fult_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2 = some (__bv_bitblast_ult_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fult_5frec
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 hinv1 s1 v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_ult_rec.case_0
  case_done hinv2 hG with h_a2 in EoCases.__bv_bitblast_ult_rec.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2 = some (__bv_bitblast_ult_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fult_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_a2 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a1 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_ult_rec.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 dropping h_v11 h_v13 he_v14 hinv2 e_v14 s2 v11 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_and.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 dropping he_v15 hinv3 e_v15 s3
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping he_v16 hinv4 e_v16 s4
  store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping h_v16 hinv5 s5 v16
  store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v15 dropping h_v17 hinv6 s6 v17
  store_step with Store.apply_rep s7 v15 v18 _ _ hinv7 h64 h_v15 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 dropping h_v15 h_v18 hinv7 s7 v15 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_and.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a2 h_v2 h_v5 h_v9 h_v12 h_v14 h_v19 dropping he_v20 hinv8 e_v20 s8
  store_step with Store.apply_rep s9 v20 a2 _ _ hinv9 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v19 dropping h_a2 h_v20 hinv9 s9 v20
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v19 h_v21 dropping hinv10 s10
  store_step with Store.apply_rep s11 v21 v22 _ _ hinv11 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 h_v19 dropping h_v21 h_v22 hinv11 s11 v21 v22
  store_step with Store.apply_rep s12 v19 v23 _ _ hinv12 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v14 dropping h_v19 h_v23 hinv12 s12 v19 v23
  store_step with Store.apply_rep s13 v14 v24 _ _ hinv13 h64 h_v14 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 dropping h_v14 h_v24 hinv13 s13 v14 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_or.construct s14 e_v26 (by rw [he_v26]; exact empty_args) hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v25 dropping he_v26 hinv14 e_v26 s14
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_and.construct s15 e_v27 (by rw [he_v27]; exact empty_args) hinv15 h64 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v25 h_v26 dropping he_v27 hinv15 e_v27 s15
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s16 e_v28 (by rw [he_v28]; exact empty_args) hinv16 h64 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v2 h_v5 h_v9 h_v12 h_v25 h_v26 h_v27 dropping he_v28 hinv16 e_v28 s16
  store_step with Store.apply_rep s17 v28 v5 _ _ hinv17 h64 h_v28 h_v5 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_v2 h_v9 h_v12 h_v25 h_v26 h_v27 dropping h_v28 h_v5 hinv17 s17 v28 v5
  store_step with Store.apply_rep s18 v27 v29 _ _ hinv18 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_v2 h_v9 h_v12 h_v25 h_v26 dropping h_v27 h_v29 hinv18 s18 v27 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_and.construct s19 e_v31 (by rw [he_v31]; exact empty_args) hinv19 h64 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_v2 h_v9 h_v12 h_v25 h_v26 h_v30 dropping he_v31 hinv19 e_v31 s19
  store_step with Store.apply_rep s20 v31 v12 _ _ hinv20 h64 h_v31 h_v12 (by ns_tac) (by ns_tac) as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_v2 h_v9 h_v25 h_v26 h_v30 dropping h_v12 h_v31 hinv20 s20 v12 v31
  store_step with Store.literal_boolean_spec s21 true hinv21 h64 as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_v2 h_v9 h_v25 h_v26 h_v30 h_v32 dropping hinv21 s21
  store_step with Store.apply_rep s22 v32 v33 _ _ hinv22 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_v2 h_v9 h_v25 h_v26 h_v30 dropping h_v32 h_v33 hinv22 s22 v32 v33
  store_step with Store.apply_rep s23 v30 v34 _ _ hinv23 h64 h_v30 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s24, hinv24, h_v35⟩ growing hG carrying h_v2 h_v9 h_v25 h_v26 dropping h_v30 h_v34 hinv23 s23 v30 v34
  store_step with Store.apply_rep s24 v26 v35 _ _ hinv24 h64 h_v26 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s25, hinv25, h_v36⟩ growing hG carrying h_v2 h_v9 h_v25 dropping h_v26 h_v35 hinv24 s24 v26 v35
  store_step with Store.literal_boolean_spec s25 false hinv25 h64 as ⟨v37, s26, hinv26, h_v37⟩ growing hG carrying h_v2 h_v9 h_v25 h_v36 dropping hinv25 s25
  store_step with Store.apply_rep s26 v36 v37 _ _ hinv26 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s27, hinv27, h_v38⟩ growing hG carrying h_v2 h_v9 h_v25 dropping h_v36 h_v37 hinv26 s26 v36 v37
  store_step with Store.apply_rep s27 v25 v38 _ _ hinv27 h64 h_v25 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s28, hinv28, h_v39⟩ growing hG carrying h_v2 h_v9 dropping h_v25 h_v38 hinv27 s27 v25 v38
  case_again hinv28 hG with h_v2 h_v9 h_v39 in EoCases.__bv_bitblast_ult_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_ult_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fult_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_ult_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_ult_rec
  unfold EoCases.__bv_bitblast_ult_rec.case_0 EoCases.__bv_bitblast_ult_rec.case_1
  logos_eq

theorem step_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __bv_bitblast_ult_rec x_a0 x_a1 x_a2 = __bv_bitblast_ult_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fult_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24bv_5fbitblast_5fult_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24bv_5fbitblast_5fult_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24bv_5fbitblast_5fult_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_ult_rec.case_0 EoCases.__bv_bitblast_ult_rec.case_1

theorem body_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24bv_5fbitblast_5fult_5frec body_eo__24bv_5fbitblast_5fult_5frec_loop
  step with step_eo__24bv_5fbitblast_5fult_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
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
      unfold body_eo__24bv_5fbitblast_5fult_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fult_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fult_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 28#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fult_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_28 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_28 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fult_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
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
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
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

theorem case_0_eo__24bv_5fdiv_5fmod_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fdiv_5fmod_5fimpl s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_div_mod_impl.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_div_mod_impl.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fdiv_5fmod_5fimpl
  have hG := Store.Grows.refl s
  pat_unapply h_a3 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_div_mod_impl.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a2 h_v1 h_v2 dropping h_a3 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_div_mod_impl.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a2 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__bv_div_mod_impl.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__40_40pair.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a2 dropping h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  store_step with Store.apply_rep s3 v5 a2 _ _ hinv3 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a2 dropping h_v5 hinv3 s3 v5
  store_step with Store.apply_rep s4 v6 a2 _ _ hinv4 h64 h_v6 h_a2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_a2 h_v6 hinv4 s4 v6
  case_done hinv5 hG with h_v7 in EoCases.__bv_div_mod_impl.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2

theorem case_1_eo__24bv_5fdiv_5fmod_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fdiv_5fmod_5fimpl s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_div_mod_impl.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_div_mod_impl.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fdiv_5fmod_5fimpl
  have hG := Store.Grows.refl s
  pat_same a2 a0 with h_a2 h_a0 using hinv else hinv hG in EoCases.__bv_div_mod_impl.case_1
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40pair.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping h_a2 he_v0 e_v0
  store_step with Store.apply_rep s1 v0 a0 _ _ hinv1 h64 h_v0 h_a0 (by ns_tac) (by ns_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 dropping h_v0 hinv1 s1 v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a0 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_div_mod_impl.case_1 using hn_a0 hn_a1 hn_a2 hn_a3

set_option maxHeartbeats 10170000 in
theorem case_2_eo__24bv_5fdiv_5fmod_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fdiv_5fmod_5fimpl s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_div_mod_impl.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_div_mod_impl.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fdiv_5fmod_5fimpl
  have hG := Store.Grows.refl s
  pat_unapply h_a3 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_div_mod_impl.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_div_mod_impl.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v4 dropping h_a3 h_v1 h_v5 he_v6 e_v6 v1 v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_div_mod_impl.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40_40pair.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_not.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_not.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s4 v9 a1 _ _ hinv4 h64 (hG.rem hrem) h_v9 h_a1 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v8 h_v10 dropping hinv5 s5
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s6 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v8 h_v10 h_v11 dropping hinv6 s6
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s7 a0 v10 v11 v12 _ _ _ _ hinv7 h64 (hG.rem hrem) h_a0 h_v10 h_v11 h_v12 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v8 dropping h_v10 h_v11 h_v12 hinv7 s7 v10 v11 v12
  store_step with ih.eo__24pair_5ffirst s8 v13 _ hinv8 h64 (hG.rem hrem) h_v13 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v8 dropping h_v13 hinv8 s8 v13
  store_step with Store.apply_mk_rep s9 v8 v14 _ _ hinv9 h64 h_v8 h_v14 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 dropping h_v14 h_v8 hinv9 s9 v14 v8
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 dropping he_v16 hinv10 e_v16 s10
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_ite.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 dropping he_v17 hinv11 e_v17 s11
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_not.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 dropping he_v18 hinv12 e_v18 s12
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s13 e_v19 (by rw [he_v19]; exact empty_args) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping he_v19 hinv13 e_v19 s13
  store_step with Store.literal_boolean_spec s14 false hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v19 dropping hinv14 s14
  store_step with Store.apply_rep s15 v19 v20 _ _ hinv15 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v19 h_v20 hinv15 s15 v19 v20
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s16 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v21 dropping hinv16 s16
  store_step with Store.apply_rep s17 v21 v22 _ _ hinv17 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v21 h_v22 hinv17 s17 v21 v22
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 dropping hinv18 s18
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 dropping he_v25 hinv19 e_v25 s19
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s20 1#u32 (1) (by scalar_tac) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 dropping hinv20 s20
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s21 e_v27 (by rw [he_v27]; exact empty_args) hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v26 dropping he_v27 hinv21 e_v27 s21
  step as ⟨e_v28, he_v28⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s22 e_v28 (by rw [he_v28]; rfl) h_v27 h_a0 hinv22 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v26 dropping h_v27 he_v28 hinv22 e_v28 s22 v27
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s23 v26 v28 a0 _ _ _ hinv23 h64 (hG.rem hrem) h_v26 h_v28 h_a0 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 dropping h_v26 h_v28 hinv23 s23 v26 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s24 e_v30 (by rw [he_v30]; exact empty_args) hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v29 dropping he_v30 hinv24 e_v30 s24
  store_step with Store.literal_boolean_spec s25 false hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v29 h_v30 dropping hinv25 s25
  store_step with Store.apply_rep s26 v30 v31 _ _ hinv26 h64 h_v30 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v29 dropping h_v30 h_v31 hinv26 s26 v30 v31
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s27 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv27 h64 as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v29 h_v32 dropping hinv27 s27
  store_step with Store.apply_rep s28 v32 v33 _ _ hinv28 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 h_v29 dropping h_v32 h_v33 hinv28 s28 v32 v33
  store_step with ih.eo__24bv_5fbitblast_5fconcat s29 v29 v34 _ _ hinv29 h64 (hG.rem hrem) h_v29 h_v34 as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 dropping h_v29 h_v34 hinv29 s29 v29 v34
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s30 v35 a1 a2 v2 _ _ _ _ hinv30 h64 (hG.rem hrem) h_v35 h_a1 h_a2 h_v2 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 dropping h_v35 hinv30 s30 v35
  store_step with ih.eo__24pair_5fsecond s31 v36 _ hinv31 h64 (hG.rem hrem) h_v36 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v25 dropping h_v36 hinv31 s31 v36
  step as ⟨e_v38, he_v38⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s32 e_v38 (by rw [he_v38]; rfl) h_v25 h_v37 hinv32 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 dropping h_v25 h_v37 he_v38 hinv32 e_v38 s32 v25 v37
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s33 1#u32 (-1) (by scalar_tac) hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v38 dropping hinv33 s33
  step as ⟨e_v40, he_v40⟩
  store_step with Store.builtin_spec_add s34 e_v40 (by rw [he_v40]; rfl) h_v38 h_v39 hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 dropping h_v38 h_v39 he_v40 hinv34 e_v40 s34 v38 v39
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s35 1#u32 (-1) (by scalar_tac) hinv35 h64 as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v40 dropping hinv35 s35
  step as ⟨e_v42, he_v42⟩
  store_step with Store.builtin_spec_add s36 e_v42 (by rw [he_v42]; rfl) h_v40 h_v41 hinv36 h64 as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 dropping h_v40 h_v41 he_v42 hinv36 e_v42 s36 v40 v41
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s37 1#u32 (1) (by scalar_tac) hinv37 h64 as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 dropping hinv37 s37
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s38 e_v44 (by rw [he_v44]; exact empty_args) hinv38 h64 as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v43 dropping he_v44 hinv38 e_v44 s38
  step as ⟨e_v45, he_v45⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s39 e_v45 (by rw [he_v45]; rfl) h_v44 h_a0 hinv39 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v43 dropping h_v44 he_v45 hinv39 e_v45 s39 v44
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s40 v43 v45 a0 _ _ _ hinv40 h64 (hG.rem hrem) h_v43 h_v45 h_a0 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 dropping h_v43 h_v45 hinv40 s40 v43 v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s41 e_v47 (by rw [he_v47]; exact empty_args) hinv41 h64 as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v46 dropping he_v47 hinv41 e_v47 s41
  store_step with Store.literal_boolean_spec s42 false hinv42 h64 as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v46 h_v47 dropping hinv42 s42
  store_step with Store.apply_rep s43 v47 v48 _ _ hinv43 h64 h_v47 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v46 dropping h_v47 h_v48 hinv43 s43 v47 v48
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s44 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv44 h64 as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v46 h_v49 dropping hinv44 s44
  store_step with Store.apply_rep s45 v49 v50 _ _ hinv45 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 h_v46 dropping h_v49 h_v50 hinv45 s45 v49 v50
  store_step with ih.eo__24bv_5fbitblast_5fconcat s46 v46 v51 _ _ hinv46 h64 (hG.rem hrem) h_v46 h_v51 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 dropping h_v46 h_v51 hinv46 s46 v46 v51
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s47 v52 a1 a2 v2 _ _ _ _ hinv47 h64 (hG.rem hrem) h_v52 h_a1 h_a2 h_v2 as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 dropping h_v52 hinv47 s47 v52
  store_step with ih.eo__24pair_5fsecond s48 v53 _ hinv48 h64 (hG.rem hrem) h_v53 as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 h_v24 h_v42 dropping h_v53 hinv48 s48 v53
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s49 v24 v42 v54 _ _ _ hinv49 h64 (hG.rem hrem) h_v24 h_v42 h_v54 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v23 dropping h_v24 h_v42 h_v54 hinv49 s49 v24 v42 v54
  store_step with ih.eo__24bv_5fbitblast_5fconcat s50 v23 v55 _ _ hinv50 h64 (hG.rem hrem) h_v23 h_v55 as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v23 h_v55 hinv50 s50 v23 v55
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_ite.construct s51 e_v57 (by rw [he_v57]; exact empty_args) hinv51 h64 as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 dropping he_v57 hinv51 e_v57 s51
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__3d.construct s52 e_v58 (by rw [he_v58]; exact empty_args) hinv52 h64 as ⟨v58, s53, hinv53, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v57 dropping he_v58 hinv52 e_v58 s52
  store_step with ih.eo__24bv_5fbitblast_5fhead s53 a0 _ hinv53 h64 (hG.rem hrem) h_a0 as ⟨v59, s54, hinv54, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v57 h_v58 dropping hinv53 s53
  store_step with Store.apply_mk_rep s54 v58 v59 _ _ hinv54 h64 h_v58 h_v59 as ⟨v60, s55, hinv55, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v57 dropping h_v58 h_v59 hinv54 s54 v58 v59
  store_step with Store.literal_boolean_spec s55 true hinv55 h64 as ⟨v61, s56, hinv56, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v57 h_v60 dropping hinv55 s55
  store_step with Store.apply_mk_rep s56 v60 v61 _ _ hinv56 h64 h_v60 h_v61 as ⟨v62, s57, hinv57, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v57 dropping h_v60 h_v61 hinv56 s56 v60 v61
  store_step with Store.apply_mk_rep s57 v57 v62 _ _ hinv57 h64 h_v57 h_v62 as ⟨v63, s58, hinv58, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 dropping h_v57 h_v62 hinv57 s57 v57 v62
  store_step with Store.literal_boolean_spec s58 true hinv58 h64 as ⟨v64, s59, hinv59, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v63 dropping hinv58 s58
  store_step with Store.apply_mk_rep s59 v63 v64 _ _ hinv59 h64 h_v63 h_v64 as ⟨v65, s60, hinv60, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 dropping h_v63 h_v64 hinv59 s59 v63 v64
  store_step with Store.literal_boolean_spec s60 false hinv60 h64 as ⟨v66, s61, hinv61, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v65 dropping hinv60 s60
  store_step with Store.apply_mk_rep s61 v65 v66 _ _ hinv61 h64 h_v65 h_v66 as ⟨v67, s62, hinv62, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 dropping h_v65 h_v66 hinv61 s61 v65 v66
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s62 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv62 h64 as ⟨v68, s63, hinv63, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v56 h_v67 dropping hinv62 s62
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s63 v56 a2 v67 v68 _ _ _ _ hinv63 h64 (hG.rem hrem) h_v56 h_a2 h_v67 h_v68 as ⟨v69, s64, hinv64, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v56 h_v67 h_v68 hinv63 s63 v56 v67 v68
  store_step with ih.eo__24pair_5fsecond s64 v69 _ hinv64 h64 (hG.rem hrem) h_v69 as ⟨v70, s65, hinv65, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v69 hinv64 s64 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_not.construct s65 e_v71 (by rw [he_v71]; exact empty_args) hinv65 h64 as ⟨v71, s66, hinv66, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v70 dropping he_v71 hinv65 e_v71 s65
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s66 v71 a1 _ _ hinv66 h64 (hG.rem hrem) h_v71 h_a1 as ⟨v72, s67, hinv67, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v70 dropping h_v71 hinv66 s66 v71
  store_step with Store.literal_boolean_spec s67 true hinv67 h64 as ⟨v73, s68, hinv68, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v70 h_v72 dropping hinv67 s67
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s68 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv68 h64 as ⟨v74, s69, hinv69, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 h_v70 h_v72 h_v73 dropping hinv68 s68
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s69 v70 v72 v73 v74 _ _ _ _ hinv69 h64 (hG.rem hrem) h_v70 h_v72 h_v73 h_v74 as ⟨v75, s70, hinv70, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v70 h_v72 h_v73 h_v74 hinv69 s69 v70 v72 v73 v74
  store_step with ih.eo__24pair_5ffirst s70 v75 _ hinv70 h64 (hG.rem hrem) h_v75 as ⟨v76, s71, hinv71, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 h_v18 dropping h_v75 hinv70 s70 v75
  store_step with Store.apply_mk_rep s71 v18 v76 _ _ hinv71 h64 h_v18 h_v76 as ⟨v77, s72, hinv72, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v17 dropping h_v18 h_v76 hinv71 s71 v18 v76
  store_step with Store.apply_mk_rep s72 v17 v77 _ _ hinv72 h64 h_v17 h_v77 as ⟨v78, s73, hinv73, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 dropping h_v17 h_v77 hinv72 s72 v17 v77
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s73 e_v79 (by rw [he_v79]; exact empty_args) hinv73 h64 as ⟨v79, s74, hinv74, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 dropping he_v79 hinv73 e_v79 s73
  store_step with Store.literal_boolean_spec s74 false hinv74 h64 as ⟨v80, s75, hinv75, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v79 dropping hinv74 s74
  store_step with Store.apply_rep s75 v79 v80 _ _ hinv75 h64 h_v79 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s76, hinv76, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 dropping h_v79 h_v80 hinv75 s75 v79 v80
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s76 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv76 h64 as ⟨v82, s77, hinv77, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v81 dropping hinv76 s76
  store_step with Store.apply_rep s77 v81 v82 _ _ hinv77 h64 h_v81 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s78, hinv78, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 dropping h_v81 h_v82 hinv77 s77 v81 v82
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s78 0#u32 (0) (by scalar_tac) hinv78 h64 as ⟨v84, s79, hinv79, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 dropping hinv78 s78
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s79 e_v85 (by rw [he_v85]; exact empty_args) hinv79 h64 as ⟨v85, s80, hinv80, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 dropping he_v85 hinv79 e_v85 s79
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s80 1#u32 (1) (by scalar_tac) hinv80 h64 as ⟨v86, s81, hinv81, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 dropping hinv80 s80
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s81 e_v87 (by rw [he_v87]; exact empty_args) hinv81 h64 as ⟨v87, s82, hinv82, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v86 dropping he_v87 hinv81 e_v87 s81
  step as ⟨e_v88, he_v88⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s82 e_v88 (by rw [he_v88]; rfl) h_v87 h_a0 hinv82 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v88, s83, hinv83, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v86 dropping h_v87 he_v88 hinv82 e_v88 s82 v87
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s83 v86 v88 a0 _ _ _ hinv83 h64 (hG.rem hrem) h_v86 h_v88 h_a0 as ⟨v89, s84, hinv84, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 dropping h_v86 h_v88 hinv83 s83 v86 v88
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s84 e_v90 (by rw [he_v90]; exact empty_args) hinv84 h64 as ⟨v90, s85, hinv85, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v89 dropping he_v90 hinv84 e_v90 s84
  store_step with Store.literal_boolean_spec s85 false hinv85 h64 as ⟨v91, s86, hinv86, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v89 h_v90 dropping hinv85 s85
  store_step with Store.apply_rep s86 v90 v91 _ _ hinv86 h64 h_v90 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s87, hinv87, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v89 dropping h_v90 h_v91 hinv86 s86 v90 v91
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s87 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv87 h64 as ⟨v93, s88, hinv88, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v89 h_v92 dropping hinv87 s87
  store_step with Store.apply_rep s88 v92 v93 _ _ hinv88 h64 h_v92 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s89, hinv89, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 h_v89 dropping h_v92 h_v93 hinv88 s88 v92 v93
  store_step with ih.eo__24bv_5fbitblast_5fconcat s89 v89 v94 _ _ hinv89 h64 (hG.rem hrem) h_v89 h_v94 as ⟨v95, s90, hinv90, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 dropping h_v89 h_v94 hinv89 s89 v89 v94
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s90 v95 a1 a2 v2 _ _ _ _ hinv90 h64 (hG.rem hrem) h_v95 h_a1 h_a2 h_v2 as ⟨v96, s91, hinv91, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 dropping h_v95 hinv90 s90 v95
  store_step with ih.eo__24pair_5ffirst s91 v96 _ hinv91 h64 (hG.rem hrem) h_v96 as ⟨v97, s92, hinv92, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v85 dropping h_v96 hinv91 s91 v96
  step as ⟨e_v98, he_v98⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s92 e_v98 (by rw [he_v98]; rfl) h_v85 h_v97 hinv92 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v98, s93, hinv93, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 dropping h_v85 h_v97 he_v98 hinv92 e_v98 s92 v85 v97
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s93 1#u32 (-1) (by scalar_tac) hinv93 h64 as ⟨v99, s94, hinv94, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v98 dropping hinv93 s93
  step as ⟨e_v100, he_v100⟩
  store_step with Store.builtin_spec_add s94 e_v100 (by rw [he_v100]; rfl) h_v98 h_v99 hinv94 h64 as ⟨v100, s95, hinv95, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 dropping h_v98 h_v99 he_v100 hinv94 e_v100 s94 v98 v99
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s95 1#u32 (-1) (by scalar_tac) hinv95 h64 as ⟨v101, s96, hinv96, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v100 dropping hinv95 s95
  step as ⟨e_v102, he_v102⟩
  store_step with Store.builtin_spec_add s96 e_v102 (by rw [he_v102]; rfl) h_v100 h_v101 hinv96 h64 as ⟨v102, s97, hinv97, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 dropping h_v100 h_v101 he_v102 hinv96 e_v102 s96 v100 v101
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s97 1#u32 (1) (by scalar_tac) hinv97 h64 as ⟨v103, s98, hinv98, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 dropping hinv97 s97
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s98 e_v104 (by rw [he_v104]; exact empty_args) hinv98 h64 as ⟨v104, s99, hinv99, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v103 dropping he_v104 hinv98 e_v104 s98
  step as ⟨e_v105, he_v105⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s99 e_v105 (by rw [he_v105]; rfl) h_v104 h_a0 hinv99 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v105, s100, hinv100, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v103 dropping h_v104 he_v105 hinv99 e_v105 s99 v104
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s100 v103 v105 a0 _ _ _ hinv100 h64 (hG.rem hrem) h_v103 h_v105 h_a0 as ⟨v106, s101, hinv101, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 dropping h_v103 h_v105 hinv100 s100 v103 v105
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s101 e_v107 (by rw [he_v107]; exact empty_args) hinv101 h64 as ⟨v107, s102, hinv102, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v106 dropping he_v107 hinv101 e_v107 s101
  store_step with Store.literal_boolean_spec s102 false hinv102 h64 as ⟨v108, s103, hinv103, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v106 h_v107 dropping hinv102 s102
  store_step with Store.apply_rep s103 v107 v108 _ _ hinv103 h64 h_v107 h_v108 (by ns_tac) (by ns_tac) as ⟨v109, s104, hinv104, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v106 dropping h_v107 h_v108 hinv103 s103 v107 v108
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s104 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv104 h64 as ⟨v110, s105, hinv105, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v106 h_v109 dropping hinv104 s104
  store_step with Store.apply_rep s105 v109 v110 _ _ hinv105 h64 h_v109 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s106, hinv106, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 h_v106 dropping h_v109 h_v110 hinv105 s105 v109 v110
  store_step with ih.eo__24bv_5fbitblast_5fconcat s106 v106 v111 _ _ hinv106 h64 (hG.rem hrem) h_v106 h_v111 as ⟨v112, s107, hinv107, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 dropping h_v106 h_v111 hinv106 s106 v106 v111
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s107 v112 a1 a2 v2 _ _ _ _ hinv107 h64 (hG.rem hrem) h_v112 h_a1 h_a2 h_v2 as ⟨v113, s108, hinv108, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 dropping h_v112 hinv107 s107 v112
  store_step with ih.eo__24pair_5ffirst s108 v113 _ hinv108 h64 (hG.rem hrem) h_v113 as ⟨v114, s109, hinv109, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 h_v84 h_v102 dropping h_v113 hinv108 s108 v113
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s109 v84 v102 v114 _ _ _ hinv109 h64 (hG.rem hrem) h_v84 h_v102 h_v114 as ⟨v115, s110, hinv110, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 h_v83 dropping h_v102 h_v114 h_v84 hinv109 s109 v102 v114 v84
  store_step with ih.eo__24bv_5fbitblast_5fconcat s110 v83 v115 _ _ hinv110 h64 (hG.rem hrem) h_v83 h_v115 as ⟨v116, s111, hinv111, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 dropping h_v115 h_v83 hinv110 s110 v115 v83
  store_step with ih.eo__24bv_5fbitblast_5fhead s111 v116 _ hinv111 h64 (hG.rem hrem) h_v116 as ⟨v117, s112, hinv112, h_v117⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v78 dropping h_v116 hinv111 s111 v116
  store_step with Store.apply_mk_rep s112 v78 v117 _ _ hinv112 h64 h_v78 h_v117 as ⟨v118, s113, hinv113, h_v118⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 dropping h_v117 h_v78 hinv112 s112 v117 v78
  store_step with Store.literal_boolean_spec s113 true hinv113 h64 as ⟨v119, s114, hinv114, h_v119⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 h_v118 dropping hinv113 s113
  store_step with Store.apply_mk_rep s114 v118 v119 _ _ hinv114 h64 h_v118 h_v119 as ⟨v120, s115, hinv115, h_v120⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v16 dropping h_v118 h_v119 hinv114 s114 v118 v119
  store_step with Store.apply_mk_rep s115 v16 v120 _ _ hinv115 h64 h_v16 h_v120 as ⟨v121, s116, hinv116, h_v121⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 dropping h_v120 h_v16 hinv115 s115 v120 v16
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s116 e_v122 (by rw [he_v122]; exact empty_args) hinv116 h64 as ⟨v122, s117, hinv117, h_v122⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 dropping he_v122 hinv116 e_v122 s116
  store_step with Store.literal_boolean_spec s117 false hinv117 h64 as ⟨v123, s118, hinv118, h_v123⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v122 dropping hinv117 s117
  store_step with Store.apply_rep s118 v122 v123 _ _ hinv118 h64 h_v122 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s119, hinv119, h_v124⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 dropping h_v122 h_v123 hinv118 s118 v122 v123
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s119 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv119 h64 as ⟨v125, s120, hinv120, h_v125⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v124 dropping hinv119 s119
  store_step with Store.apply_rep s120 v124 v125 _ _ hinv120 h64 h_v124 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s121, hinv121, h_v126⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 dropping h_v124 h_v125 hinv120 s120 v124 v125
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s121 0#u32 (0) (by scalar_tac) hinv121 h64 as ⟨v127, s122, hinv122, h_v127⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 dropping hinv121 s121
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s122 e_v128 (by rw [he_v128]; exact empty_args) hinv122 h64 as ⟨v128, s123, hinv123, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 dropping he_v128 hinv122 e_v128 s122
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s123 1#u32 (1) (by scalar_tac) hinv123 h64 as ⟨v129, s124, hinv124, h_v129⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 dropping hinv123 s123
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s124 e_v130 (by rw [he_v130]; exact empty_args) hinv124 h64 as ⟨v130, s125, hinv125, h_v130⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v129 dropping he_v130 hinv124 e_v130 s124
  step as ⟨e_v131, he_v131⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s125 e_v131 (by rw [he_v131]; rfl) h_v130 h_a0 hinv125 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v131, s126, hinv126, h_v131⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v129 dropping h_v130 he_v131 hinv125 e_v131 s125 v130
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s126 v129 v131 a0 _ _ _ hinv126 h64 (hG.rem hrem) h_v129 h_v131 h_a0 as ⟨v132, s127, hinv127, h_v132⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 dropping h_v129 h_v131 hinv126 s126 v129 v131
  step as ⟨e_v133, he_v133⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s127 e_v133 (by rw [he_v133]; exact empty_args) hinv127 h64 as ⟨v133, s128, hinv128, h_v133⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v132 dropping he_v133 hinv127 e_v133 s127
  store_step with Store.literal_boolean_spec s128 false hinv128 h64 as ⟨v134, s129, hinv129, h_v134⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v132 h_v133 dropping hinv128 s128
  store_step with Store.apply_rep s129 v133 v134 _ _ hinv129 h64 h_v133 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s130, hinv130, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v132 dropping h_v133 h_v134 hinv129 s129 v133 v134
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s130 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv130 h64 as ⟨v136, s131, hinv131, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v132 h_v135 dropping hinv130 s130
  store_step with Store.apply_rep s131 v135 v136 _ _ hinv131 h64 h_v135 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s132, hinv132, h_v137⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 h_v132 dropping h_v135 h_v136 hinv131 s131 v135 v136
  store_step with ih.eo__24bv_5fbitblast_5fconcat s132 v132 v137 _ _ hinv132 h64 (hG.rem hrem) h_v132 h_v137 as ⟨v138, s133, hinv133, h_v138⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 dropping h_v132 h_v137 hinv132 s132 v132 v137
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s133 v138 a1 a2 v2 _ _ _ _ hinv133 h64 (hG.rem hrem) h_v138 h_a1 h_a2 h_v2 as ⟨v139, s134, hinv134, h_v139⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 dropping h_v138 hinv133 s133 v138
  store_step with ih.eo__24pair_5ffirst s134 v139 _ hinv134 h64 (hG.rem hrem) h_v139 as ⟨v140, s135, hinv135, h_v140⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v128 dropping h_v139 hinv134 s134 v139
  step as ⟨e_v141, he_v141⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s135 e_v141 (by rw [he_v141]; rfl) h_v128 h_v140 hinv135 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v141, s136, hinv136, h_v141⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 dropping h_v128 h_v140 he_v141 hinv135 e_v141 s135 v128 v140
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s136 1#u32 (-1) (by scalar_tac) hinv136 h64 as ⟨v142, s137, hinv137, h_v142⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v141 dropping hinv136 s136
  step as ⟨e_v143, he_v143⟩
  store_step with Store.builtin_spec_add s137 e_v143 (by rw [he_v143]; rfl) h_v141 h_v142 hinv137 h64 as ⟨v143, s138, hinv138, h_v143⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 dropping h_v141 h_v142 he_v143 hinv137 e_v143 s137 v141 v142
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s138 1#u32 (-1) (by scalar_tac) hinv138 h64 as ⟨v144, s139, hinv139, h_v144⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v143 dropping hinv138 s138
  step as ⟨e_v145, he_v145⟩
  store_step with Store.builtin_spec_add s139 e_v145 (by rw [he_v145]; rfl) h_v143 h_v144 hinv139 h64 as ⟨v145, s140, hinv140, h_v145⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 dropping h_v143 h_v144 he_v145 hinv139 e_v145 s139 v143 v144
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s140 1#u32 (1) (by scalar_tac) hinv140 h64 as ⟨v146, s141, hinv141, h_v146⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 dropping hinv140 s140
  step as ⟨e_v147, he_v147⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s141 e_v147 (by rw [he_v147]; exact empty_args) hinv141 h64 as ⟨v147, s142, hinv142, h_v147⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v146 dropping he_v147 hinv141 e_v147 s141
  step as ⟨e_v148, he_v148⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s142 e_v148 (by rw [he_v148]; rfl) h_v147 h_a0 hinv142 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v148, s143, hinv143, h_v148⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v146 dropping h_v147 he_v148 hinv142 e_v148 s142 v147
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s143 v146 v148 a0 _ _ _ hinv143 h64 (hG.rem hrem) h_v146 h_v148 h_a0 as ⟨v149, s144, hinv144, h_v149⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 dropping h_v146 h_v148 hinv143 s143 v146 v148
  step as ⟨e_v150, he_v150⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s144 e_v150 (by rw [he_v150]; exact empty_args) hinv144 h64 as ⟨v150, s145, hinv145, h_v150⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v149 dropping he_v150 hinv144 e_v150 s144
  store_step with Store.literal_boolean_spec s145 false hinv145 h64 as ⟨v151, s146, hinv146, h_v151⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v149 h_v150 dropping hinv145 s145
  store_step with Store.apply_rep s146 v150 v151 _ _ hinv146 h64 h_v150 h_v151 (by ns_tac) (by ns_tac) as ⟨v152, s147, hinv147, h_v152⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v149 dropping h_v150 h_v151 hinv146 s146 v150 v151
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s147 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv147 h64 as ⟨v153, s148, hinv148, h_v153⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v149 h_v152 dropping hinv147 s147
  store_step with Store.apply_rep s148 v152 v153 _ _ hinv148 h64 h_v152 h_v153 (by ns_tac) (by ns_tac) as ⟨v154, s149, hinv149, h_v154⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 h_v149 dropping h_v152 h_v153 hinv148 s148 v152 v153
  store_step with ih.eo__24bv_5fbitblast_5fconcat s149 v149 v154 _ _ hinv149 h64 (hG.rem hrem) h_v149 h_v154 as ⟨v155, s150, hinv150, h_v155⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 dropping h_v149 h_v154 hinv149 s149 v149 v154
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s150 v155 a1 a2 v2 _ _ _ _ hinv150 h64 (hG.rem hrem) h_v155 h_a1 h_a2 h_v2 as ⟨v156, s151, hinv151, h_v156⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 dropping h_v155 hinv150 s150 v155
  store_step with ih.eo__24pair_5ffirst s151 v156 _ hinv151 h64 (hG.rem hrem) h_v156 as ⟨v157, s152, hinv152, h_v157⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 h_v127 h_v145 dropping h_v156 hinv151 s151 v156
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s152 v127 v145 v157 _ _ _ hinv152 h64 (hG.rem hrem) h_v127 h_v145 h_v157 as ⟨v158, s153, hinv153, h_v158⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 h_v126 dropping h_v127 h_v145 h_v157 hinv152 s152 v127 v145 v157
  store_step with ih.eo__24bv_5fbitblast_5fconcat s153 v126 v158 _ _ hinv153 h64 (hG.rem hrem) h_v126 h_v158 as ⟨v159, s154, hinv154, h_v159⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 dropping h_v126 h_v158 hinv153 s153 v126 v158
  store_step with ih.eo__24bv_5fbitblast_5ftail s154 v159 _ hinv154 h64 (hG.rem hrem) h_v159 as ⟨v160, s155, hinv155, h_v160⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 h_v121 dropping h_v159 hinv154 s154 v159
  store_step with Store.apply_mk_rep s155 v121 v160 _ _ hinv155 h64 h_v121 h_v160 as ⟨v161, s156, hinv156, h_v161⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 h_v15 dropping h_v121 h_v160 hinv155 s155 v121 v160
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fite s156 v15 a2 v161 _ _ _ hinv156 h64 (hG.rem hrem) h_v15 h_a2 h_v161 as ⟨v162, s157, hinv157, h_v162⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v7 dropping h_v15 h_v161 hinv156 s156 v15 v161
  store_step with Store.apply_mk_rep s157 v7 v162 _ _ hinv157 h64 h_v7 h_v162 as ⟨v163, s158, hinv158, h_v163⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 dropping h_v162 h_v7 hinv157 s157 v162 v7
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo_not.construct s158 e_v164 (by rw [he_v164]; exact empty_args) hinv158 h64 as ⟨v164, s159, hinv159, h_v164⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 dropping he_v164 hinv158 e_v164 s158
  step as ⟨e_v165, he_v165⟩
  store_step with CtorSpec.eo_not.construct s159 e_v165 (by rw [he_v165]; exact empty_args) hinv159 h64 as ⟨v165, s160, hinv160, h_v165⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v164 dropping he_v165 hinv159 e_v165 s159
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s160 v165 a1 _ _ hinv160 h64 (hG.rem hrem) h_v165 h_a1 as ⟨v166, s161, hinv161, h_v166⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v164 dropping h_v165 hinv160 s160 v165
  store_step with Store.literal_boolean_spec s161 true hinv161 h64 as ⟨v167, s162, hinv162, h_v167⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v164 h_v166 dropping hinv161 s161
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s162 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv162 h64 as ⟨v168, s163, hinv163, h_v168⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v164 h_v166 h_v167 dropping hinv162 s162
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s163 a0 v166 v167 v168 _ _ _ _ hinv163 h64 (hG.rem hrem) h_a0 h_v166 h_v167 h_v168 as ⟨v169, s164, hinv164, h_v169⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v164 dropping h_v166 h_v167 h_v168 hinv163 s163 v166 v167 v168
  store_step with ih.eo__24pair_5ffirst s164 v169 _ hinv164 h64 (hG.rem hrem) h_v169 as ⟨v170, s165, hinv165, h_v170⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v164 dropping h_v169 hinv164 s164 v169
  store_step with Store.apply_mk_rep s165 v164 v170 _ _ hinv165 h64 h_v164 h_v170 as ⟨v171, s166, hinv166, h_v171⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 dropping h_v164 h_v170 hinv165 s165 v164 v170
  step as ⟨e_v172, he_v172⟩
  store_step with CtorSpec.eo_not.construct s166 e_v172 (by rw [he_v172]; exact empty_args) hinv166 h64 as ⟨v172, s167, hinv167, h_v172⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 dropping he_v172 hinv166 e_v172 s166
  step as ⟨e_v173, he_v173⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s167 e_v173 (by rw [he_v173]; exact empty_args) hinv167 h64 as ⟨v173, s168, hinv168, h_v173⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping he_v173 hinv167 e_v173 s167
  store_step with Store.literal_boolean_spec s168 false hinv168 h64 as ⟨v174, s169, hinv169, h_v174⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v173 dropping hinv168 s168
  store_step with Store.apply_rep s169 v173 v174 _ _ hinv169 h64 h_v173 h_v174 (by ns_tac) (by ns_tac) as ⟨v175, s170, hinv170, h_v175⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v173 h_v174 hinv169 s169 v173 v174
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s170 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv170 h64 as ⟨v176, s171, hinv171, h_v176⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v175 dropping hinv170 s170
  store_step with Store.apply_rep s171 v175 v176 _ _ hinv171 h64 h_v175 h_v176 (by ns_tac) (by ns_tac) as ⟨v177, s172, hinv172, h_v177⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v175 h_v176 hinv171 s171 v175 v176
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s172 0#u32 (0) (by scalar_tac) hinv172 h64 as ⟨v178, s173, hinv173, h_v178⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 dropping hinv172 s172
  step as ⟨e_v179, he_v179⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s173 e_v179 (by rw [he_v179]; exact empty_args) hinv173 h64 as ⟨v179, s174, hinv174, h_v179⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 dropping he_v179 hinv173 e_v179 s173
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s174 1#u32 (1) (by scalar_tac) hinv174 h64 as ⟨v180, s175, hinv175, h_v180⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 dropping hinv174 s174
  step as ⟨e_v181, he_v181⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s175 e_v181 (by rw [he_v181]; exact empty_args) hinv175 h64 as ⟨v181, s176, hinv176, h_v181⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v180 dropping he_v181 hinv175 e_v181 s175
  step as ⟨e_v182, he_v182⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s176 e_v182 (by rw [he_v182]; rfl) h_v181 h_a0 hinv176 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v182, s177, hinv177, h_v182⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v180 dropping h_v181 he_v182 hinv176 e_v182 s176 v181
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s177 v180 v182 a0 _ _ _ hinv177 h64 (hG.rem hrem) h_v180 h_v182 h_a0 as ⟨v183, s178, hinv178, h_v183⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v180 h_v182 hinv177 s177 v180 v182
  step as ⟨e_v184, he_v184⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s178 e_v184 (by rw [he_v184]; exact empty_args) hinv178 h64 as ⟨v184, s179, hinv179, h_v184⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v183 dropping he_v184 hinv178 e_v184 s178
  store_step with Store.literal_boolean_spec s179 false hinv179 h64 as ⟨v185, s180, hinv180, h_v185⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v183 h_v184 dropping hinv179 s179
  store_step with Store.apply_rep s180 v184 v185 _ _ hinv180 h64 h_v184 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s181, hinv181, h_v186⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v183 dropping h_v184 h_v185 hinv180 s180 v184 v185
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s181 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv181 h64 as ⟨v187, s182, hinv182, h_v187⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v183 h_v186 dropping hinv181 s181
  store_step with Store.apply_rep s182 v186 v187 _ _ hinv182 h64 h_v186 h_v187 (by ns_tac) (by ns_tac) as ⟨v188, s183, hinv183, h_v188⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 h_v183 dropping h_v186 h_v187 hinv182 s182 v186 v187
  store_step with ih.eo__24bv_5fbitblast_5fconcat s183 v183 v188 _ _ hinv183 h64 (hG.rem hrem) h_v183 h_v188 as ⟨v189, s184, hinv184, h_v189⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v183 h_v188 hinv183 s183 v183 v188
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s184 v189 a1 a2 v2 _ _ _ _ hinv184 h64 (hG.rem hrem) h_v189 h_a1 h_a2 h_v2 as ⟨v190, s185, hinv185, h_v190⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v189 hinv184 s184 v189
  store_step with ih.eo__24pair_5fsecond s185 v190 _ hinv185 h64 (hG.rem hrem) h_v190 as ⟨v191, s186, hinv186, h_v191⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v190 hinv185 s185 v190
  step as ⟨e_v192, he_v192⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s186 e_v192 (by rw [he_v192]; rfl) h_v179 h_v191 hinv186 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v192, s187, hinv187, h_v192⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 dropping h_v179 h_v191 he_v192 hinv186 e_v192 s186 v179 v191
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s187 1#u32 (-1) (by scalar_tac) hinv187 h64 as ⟨v193, s188, hinv188, h_v193⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v192 dropping hinv187 s187
  step as ⟨e_v194, he_v194⟩
  store_step with Store.builtin_spec_add s188 e_v194 (by rw [he_v194]; rfl) h_v192 h_v193 hinv188 h64 as ⟨v194, s189, hinv189, h_v194⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 dropping h_v192 h_v193 he_v194 hinv188 e_v194 s188 v192 v193
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s189 1#u32 (-1) (by scalar_tac) hinv189 h64 as ⟨v195, s190, hinv190, h_v195⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v194 dropping hinv189 s189
  step as ⟨e_v196, he_v196⟩
  store_step with Store.builtin_spec_add s190 e_v196 (by rw [he_v196]; rfl) h_v194 h_v195 hinv190 h64 as ⟨v196, s191, hinv191, h_v196⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 dropping h_v194 h_v195 he_v196 hinv190 e_v196 s190 v194 v195
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s191 1#u32 (1) (by scalar_tac) hinv191 h64 as ⟨v197, s192, hinv192, h_v197⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 dropping hinv191 s191
  step as ⟨e_v198, he_v198⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s192 e_v198 (by rw [he_v198]; exact empty_args) hinv192 h64 as ⟨v198, s193, hinv193, h_v198⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v197 dropping he_v198 hinv192 e_v198 s192
  step as ⟨e_v199, he_v199⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s193 e_v199 (by rw [he_v199]; rfl) h_v198 h_a0 hinv193 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v199, s194, hinv194, h_v199⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v197 dropping h_v198 he_v199 hinv193 e_v199 s193 v198
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s194 v197 v199 a0 _ _ _ hinv194 h64 (hG.rem hrem) h_v197 h_v199 h_a0 as ⟨v200, s195, hinv195, h_v200⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 dropping h_v197 h_v199 hinv194 s194 v197 v199
  step as ⟨e_v201, he_v201⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s195 e_v201 (by rw [he_v201]; exact empty_args) hinv195 h64 as ⟨v201, s196, hinv196, h_v201⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v200 dropping he_v201 hinv195 e_v201 s195
  store_step with Store.literal_boolean_spec s196 false hinv196 h64 as ⟨v202, s197, hinv197, h_v202⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v200 h_v201 dropping hinv196 s196
  store_step with Store.apply_rep s197 v201 v202 _ _ hinv197 h64 h_v201 h_v202 (by ns_tac) (by ns_tac) as ⟨v203, s198, hinv198, h_v203⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v200 dropping h_v201 h_v202 hinv197 s197 v201 v202
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s198 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv198 h64 as ⟨v204, s199, hinv199, h_v204⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v200 h_v203 dropping hinv198 s198
  store_step with Store.apply_rep s199 v203 v204 _ _ hinv199 h64 h_v203 h_v204 (by ns_tac) (by ns_tac) as ⟨v205, s200, hinv200, h_v205⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 h_v200 dropping h_v203 h_v204 hinv199 s199 v203 v204
  store_step with ih.eo__24bv_5fbitblast_5fconcat s200 v200 v205 _ _ hinv200 h64 (hG.rem hrem) h_v200 h_v205 as ⟨v206, s201, hinv201, h_v206⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 dropping h_v200 h_v205 hinv200 s200 v200 v205
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s201 v206 a1 a2 v2 _ _ _ _ hinv201 h64 (hG.rem hrem) h_v206 h_a1 h_a2 h_v2 as ⟨v207, s202, hinv202, h_v207⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 dropping h_v206 hinv201 s201 v206
  store_step with ih.eo__24pair_5fsecond s202 v207 _ hinv202 h64 (hG.rem hrem) h_v207 as ⟨v208, s203, hinv203, h_v208⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 h_v178 h_v196 dropping h_v207 hinv202 s202 v207
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s203 v178 v196 v208 _ _ _ hinv203 h64 (hG.rem hrem) h_v178 h_v196 h_v208 as ⟨v209, s204, hinv204, h_v209⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v177 dropping h_v178 h_v196 h_v208 hinv203 s203 v178 v196 v208
  store_step with ih.eo__24bv_5fbitblast_5fconcat s204 v177 v209 _ _ hinv204 h64 (hG.rem hrem) h_v177 h_v209 as ⟨v210, s205, hinv205, h_v210⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v177 h_v209 hinv204 s204 v177 v209
  step as ⟨e_v211, he_v211⟩
  store_step with CtorSpec.eo_ite.construct s205 e_v211 (by rw [he_v211]; exact empty_args) hinv205 h64 as ⟨v211, s206, hinv206, h_v211⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 dropping he_v211 hinv205 e_v211 s205
  step as ⟨e_v212, he_v212⟩
  store_step with CtorSpec.eo__3d.construct s206 e_v212 (by rw [he_v212]; exact empty_args) hinv206 h64 as ⟨v212, s207, hinv207, h_v212⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v211 dropping he_v212 hinv206 e_v212 s206
  store_step with ih.eo__24bv_5fbitblast_5fhead s207 a0 _ hinv207 h64 (hG.rem hrem) h_a0 as ⟨v213, s208, hinv208, h_v213⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v211 h_v212 dropping hinv207 s207
  store_step with Store.apply_mk_rep s208 v212 v213 _ _ hinv208 h64 h_v212 h_v213 as ⟨v214, s209, hinv209, h_v214⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v211 dropping h_v212 h_v213 hinv208 s208 v212 v213
  store_step with Store.literal_boolean_spec s209 true hinv209 h64 as ⟨v215, s210, hinv210, h_v215⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v211 h_v214 dropping hinv209 s209
  store_step with Store.apply_mk_rep s210 v214 v215 _ _ hinv210 h64 h_v214 h_v215 as ⟨v216, s211, hinv211, h_v216⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v211 dropping h_v214 h_v215 hinv210 s210 v214 v215
  store_step with Store.apply_mk_rep s211 v211 v216 _ _ hinv211 h64 h_v211 h_v216 as ⟨v217, s212, hinv212, h_v217⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 dropping h_v211 h_v216 hinv211 s211 v211 v216
  store_step with Store.literal_boolean_spec s212 true hinv212 h64 as ⟨v218, s213, hinv213, h_v218⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v217 dropping hinv212 s212
  store_step with Store.apply_mk_rep s213 v217 v218 _ _ hinv213 h64 h_v217 h_v218 as ⟨v219, s214, hinv214, h_v219⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 dropping h_v217 h_v218 hinv213 s213 v217 v218
  store_step with Store.literal_boolean_spec s214 false hinv214 h64 as ⟨v220, s215, hinv215, h_v220⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v219 dropping hinv214 s214
  store_step with Store.apply_mk_rep s215 v219 v220 _ _ hinv215 h64 h_v219 h_v220 as ⟨v221, s216, hinv216, h_v221⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 dropping h_v219 h_v220 hinv215 s215 v219 v220
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s216 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv216 h64 as ⟨v222, s217, hinv217, h_v222⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v210 h_v221 dropping hinv216 s216
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s217 v210 a2 v221 v222 _ _ _ _ hinv217 h64 (hG.rem hrem) h_v210 h_a2 h_v221 h_v222 as ⟨v223, s218, hinv218, h_v223⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v210 h_v221 h_v222 hinv217 s217 v210 v221 v222
  store_step with ih.eo__24pair_5fsecond s218 v223 _ hinv218 h64 (hG.rem hrem) h_v223 as ⟨v224, s219, hinv219, h_v224⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v223 hinv218 s218 v223
  step as ⟨e_v225, he_v225⟩
  store_step with CtorSpec.eo_not.construct s219 e_v225 (by rw [he_v225]; exact empty_args) hinv219 h64 as ⟨v225, s220, hinv220, h_v225⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v224 dropping he_v225 hinv219 e_v225 s219
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s220 v225 a1 _ _ hinv220 h64 (hG.rem hrem) h_v225 h_a1 as ⟨v226, s221, hinv221, h_v226⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v224 dropping h_v225 hinv220 s220 v225
  store_step with Store.literal_boolean_spec s221 true hinv221 h64 as ⟨v227, s222, hinv222, h_v227⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v224 h_v226 dropping hinv221 s221
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s222 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv222 h64 as ⟨v228, s223, hinv223, h_v228⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 h_v224 h_v226 h_v227 dropping hinv222 s222
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s223 v224 v226 v227 v228 _ _ _ _ hinv223 h64 (hG.rem hrem) h_v224 h_v226 h_v227 h_v228 as ⟨v229, s224, hinv224, h_v229⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v224 h_v226 h_v227 h_v228 hinv223 s223 v224 v226 v227 v228
  store_step with ih.eo__24pair_5ffirst s224 v229 _ hinv224 h64 (hG.rem hrem) h_v229 as ⟨v230, s225, hinv225, h_v230⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v172 dropping h_v229 hinv224 s224 v229
  store_step with Store.apply_mk_rep s225 v172 v230 _ _ hinv225 h64 h_v172 h_v230 as ⟨v231, s226, hinv226, h_v231⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 dropping h_v172 h_v230 hinv225 s225 v172 v230
  step as ⟨e_v232, he_v232⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s226 e_v232 (by rw [he_v232]; exact empty_args) hinv226 h64 as ⟨v232, s227, hinv227, h_v232⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 dropping he_v232 hinv226 e_v232 s226
  store_step with Store.literal_boolean_spec s227 false hinv227 h64 as ⟨v233, s228, hinv228, h_v233⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v232 dropping hinv227 s227
  store_step with Store.apply_rep s228 v232 v233 _ _ hinv228 h64 h_v232 h_v233 (by ns_tac) (by ns_tac) as ⟨v234, s229, hinv229, h_v234⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 dropping h_v232 h_v233 hinv228 s228 v232 v233
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s229 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv229 h64 as ⟨v235, s230, hinv230, h_v235⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v234 dropping hinv229 s229
  store_step with Store.apply_rep s230 v234 v235 _ _ hinv230 h64 h_v234 h_v235 (by ns_tac) (by ns_tac) as ⟨v236, s231, hinv231, h_v236⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 dropping h_v234 h_v235 hinv230 s230 v234 v235
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s231 0#u32 (0) (by scalar_tac) hinv231 h64 as ⟨v237, s232, hinv232, h_v237⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 dropping hinv231 s231
  step as ⟨e_v238, he_v238⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s232 e_v238 (by rw [he_v238]; exact empty_args) hinv232 h64 as ⟨v238, s233, hinv233, h_v238⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 dropping he_v238 hinv232 e_v238 s232
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s233 1#u32 (1) (by scalar_tac) hinv233 h64 as ⟨v239, s234, hinv234, h_v239⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 dropping hinv233 s233
  step as ⟨e_v240, he_v240⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s234 e_v240 (by rw [he_v240]; exact empty_args) hinv234 h64 as ⟨v240, s235, hinv235, h_v240⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v239 dropping he_v240 hinv234 e_v240 s234
  step as ⟨e_v241, he_v241⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s235 e_v241 (by rw [he_v241]; rfl) h_v240 h_a0 hinv235 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v241, s236, hinv236, h_v241⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v239 dropping h_v240 he_v241 hinv235 e_v241 s235 v240
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s236 v239 v241 a0 _ _ _ hinv236 h64 (hG.rem hrem) h_v239 h_v241 h_a0 as ⟨v242, s237, hinv237, h_v242⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 dropping h_v239 h_v241 hinv236 s236 v239 v241
  step as ⟨e_v243, he_v243⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s237 e_v243 (by rw [he_v243]; exact empty_args) hinv237 h64 as ⟨v243, s238, hinv238, h_v243⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v242 dropping he_v243 hinv237 e_v243 s237
  store_step with Store.literal_boolean_spec s238 false hinv238 h64 as ⟨v244, s239, hinv239, h_v244⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v242 h_v243 dropping hinv238 s238
  store_step with Store.apply_rep s239 v243 v244 _ _ hinv239 h64 h_v243 h_v244 (by ns_tac) (by ns_tac) as ⟨v245, s240, hinv240, h_v245⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v242 dropping h_v243 h_v244 hinv239 s239 v243 v244
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s240 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv240 h64 as ⟨v246, s241, hinv241, h_v246⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v242 h_v245 dropping hinv240 s240
  store_step with Store.apply_rep s241 v245 v246 _ _ hinv241 h64 h_v245 h_v246 (by ns_tac) (by ns_tac) as ⟨v247, s242, hinv242, h_v247⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 h_v242 dropping h_v245 h_v246 hinv241 s241 v245 v246
  store_step with ih.eo__24bv_5fbitblast_5fconcat s242 v242 v247 _ _ hinv242 h64 (hG.rem hrem) h_v242 h_v247 as ⟨v248, s243, hinv243, h_v248⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 dropping h_v242 h_v247 hinv242 s242 v242 v247
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s243 v248 a1 a2 v2 _ _ _ _ hinv243 h64 (hG.rem hrem) h_v248 h_a1 h_a2 h_v2 as ⟨v249, s244, hinv244, h_v249⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 dropping h_v248 hinv243 s243 v248
  store_step with ih.eo__24pair_5fsecond s244 v249 _ hinv244 h64 (hG.rem hrem) h_v249 as ⟨v250, s245, hinv245, h_v250⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v238 dropping h_v249 hinv244 s244 v249
  step as ⟨e_v251, he_v251⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s245 e_v251 (by rw [he_v251]; rfl) h_v238 h_v250 hinv245 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v251, s246, hinv246, h_v251⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 dropping h_v238 h_v250 he_v251 hinv245 e_v251 s245 v238 v250
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s246 1#u32 (-1) (by scalar_tac) hinv246 h64 as ⟨v252, s247, hinv247, h_v252⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v251 dropping hinv246 s246
  step as ⟨e_v253, he_v253⟩
  store_step with Store.builtin_spec_add s247 e_v253 (by rw [he_v253]; rfl) h_v251 h_v252 hinv247 h64 as ⟨v253, s248, hinv248, h_v253⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 dropping h_v251 h_v252 he_v253 hinv247 e_v253 s247 v251 v252
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s248 1#u32 (-1) (by scalar_tac) hinv248 h64 as ⟨v254, s249, hinv249, h_v254⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v253 dropping hinv248 s248
  step as ⟨e_v255, he_v255⟩
  store_step with Store.builtin_spec_add s249 e_v255 (by rw [he_v255]; rfl) h_v253 h_v254 hinv249 h64 as ⟨v255, s250, hinv250, h_v255⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 dropping h_v253 h_v254 he_v255 hinv249 e_v255 s249 v253 v254
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s250 1#u32 (1) (by scalar_tac) hinv250 h64 as ⟨v256, s251, hinv251, h_v256⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 dropping hinv250 s250
  step as ⟨e_v257, he_v257⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s251 e_v257 (by rw [he_v257]; exact empty_args) hinv251 h64 as ⟨v257, s252, hinv252, h_v257⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v256 dropping he_v257 hinv251 e_v257 s251
  step as ⟨e_v258, he_v258⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s252 e_v258 (by rw [he_v258]; rfl) h_v257 h_a0 hinv252 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v258, s253, hinv253, h_v258⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v256 dropping h_v257 he_v258 hinv252 e_v258 s252 v257
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s253 v256 v258 a0 _ _ _ hinv253 h64 (hG.rem hrem) h_v256 h_v258 h_a0 as ⟨v259, s254, hinv254, h_v259⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 dropping h_v256 h_v258 hinv253 s253 v256 v258
  step as ⟨e_v260, he_v260⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s254 e_v260 (by rw [he_v260]; exact empty_args) hinv254 h64 as ⟨v260, s255, hinv255, h_v260⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v259 dropping he_v260 hinv254 e_v260 s254
  store_step with Store.literal_boolean_spec s255 false hinv255 h64 as ⟨v261, s256, hinv256, h_v261⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v259 h_v260 dropping hinv255 s255
  store_step with Store.apply_rep s256 v260 v261 _ _ hinv256 h64 h_v260 h_v261 (by ns_tac) (by ns_tac) as ⟨v262, s257, hinv257, h_v262⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v259 dropping h_v260 h_v261 hinv256 s256 v260 v261
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s257 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv257 h64 as ⟨v263, s258, hinv258, h_v263⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v259 h_v262 dropping hinv257 s257
  store_step with Store.apply_rep s258 v262 v263 _ _ hinv258 h64 h_v262 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s259, hinv259, h_v264⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 h_v259 dropping h_v262 h_v263 hinv258 s258 v262 v263
  store_step with ih.eo__24bv_5fbitblast_5fconcat s259 v259 v264 _ _ hinv259 h64 (hG.rem hrem) h_v259 h_v264 as ⟨v265, s260, hinv260, h_v265⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 dropping h_v259 h_v264 hinv259 s259 v259 v264
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s260 v265 a1 a2 v2 _ _ _ _ hinv260 h64 (hG.rem hrem) h_v265 h_a1 h_a2 h_v2 as ⟨v266, s261, hinv261, h_v266⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 dropping h_v265 hinv260 s260 v265
  store_step with ih.eo__24pair_5fsecond s261 v266 _ hinv261 h64 (hG.rem hrem) h_v266 as ⟨v267, s262, hinv262, h_v267⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 h_v237 h_v255 dropping h_v266 hinv261 s261 v266
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s262 v237 v255 v267 _ _ _ hinv262 h64 (hG.rem hrem) h_v237 h_v255 h_v267 as ⟨v268, s263, hinv263, h_v268⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v236 dropping h_v237 h_v255 h_v267 hinv262 s262 v237 v255 v267
  store_step with ih.eo__24bv_5fbitblast_5fconcat s263 v236 v268 _ _ hinv263 h64 (hG.rem hrem) h_v236 h_v268 as ⟨v269, s264, hinv264, h_v269⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 dropping h_v236 h_v268 hinv263 s263 v236 v268
  step as ⟨e_v270, he_v270⟩
  store_step with CtorSpec.eo_ite.construct s264 e_v270 (by rw [he_v270]; exact empty_args) hinv264 h64 as ⟨v270, s265, hinv265, h_v270⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 dropping he_v270 hinv264 e_v270 s264
  step as ⟨e_v271, he_v271⟩
  store_step with CtorSpec.eo__3d.construct s265 e_v271 (by rw [he_v271]; exact empty_args) hinv265 h64 as ⟨v271, s266, hinv266, h_v271⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v270 dropping he_v271 hinv265 e_v271 s265
  store_step with ih.eo__24bv_5fbitblast_5fhead s266 a0 _ hinv266 h64 (hG.rem hrem) h_a0 as ⟨v272, s267, hinv267, h_v272⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v270 h_v271 dropping hinv266 s266
  store_step with Store.apply_mk_rep s267 v271 v272 _ _ hinv267 h64 h_v271 h_v272 as ⟨v273, s268, hinv268, h_v273⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v270 dropping h_v271 h_v272 hinv267 s267 v271 v272
  store_step with Store.literal_boolean_spec s268 true hinv268 h64 as ⟨v274, s269, hinv269, h_v274⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v270 h_v273 dropping hinv268 s268
  store_step with Store.apply_mk_rep s269 v273 v274 _ _ hinv269 h64 h_v273 h_v274 as ⟨v275, s270, hinv270, h_v275⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v270 dropping h_v273 h_v274 hinv269 s269 v273 v274
  store_step with Store.apply_mk_rep s270 v270 v275 _ _ hinv270 h64 h_v270 h_v275 as ⟨v276, s271, hinv271, h_v276⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 dropping h_v270 h_v275 hinv270 s270 v270 v275
  store_step with Store.literal_boolean_spec s271 true hinv271 h64 as ⟨v277, s272, hinv272, h_v277⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v276 dropping hinv271 s271
  store_step with Store.apply_mk_rep s272 v276 v277 _ _ hinv272 h64 h_v276 h_v277 as ⟨v278, s273, hinv273, h_v278⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 dropping h_v276 h_v277 hinv272 s272 v276 v277
  store_step with Store.literal_boolean_spec s273 false hinv273 h64 as ⟨v279, s274, hinv274, h_v279⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v278 dropping hinv273 s273
  store_step with Store.apply_mk_rep s274 v278 v279 _ _ hinv274 h64 h_v278 h_v279 as ⟨v280, s275, hinv275, h_v280⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 dropping h_v278 h_v279 hinv274 s274 v278 v279
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s275 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv275 h64 as ⟨v281, s276, hinv276, h_v281⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v269 h_v280 dropping hinv275 s275
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s276 v269 a2 v280 v281 _ _ _ _ hinv276 h64 (hG.rem hrem) h_v269 h_a2 h_v280 h_v281 as ⟨v282, s277, hinv277, h_v282⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 dropping h_v269 h_v280 h_v281 hinv276 s276 v269 v280 v281
  store_step with ih.eo__24pair_5fsecond s277 v282 _ hinv277 h64 (hG.rem hrem) h_v282 as ⟨v283, s278, hinv278, h_v283⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 dropping h_v282 hinv277 s277 v282
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s278 e_v284 (by rw [he_v284]; exact empty_args) hinv278 h64 as ⟨v284, s279, hinv279, h_v284⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 dropping he_v284 hinv278 e_v284 s278
  store_step with Store.literal_boolean_spec s279 false hinv279 h64 as ⟨v285, s280, hinv280, h_v285⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v284 dropping hinv279 s279
  store_step with Store.apply_rep s280 v284 v285 _ _ hinv280 h64 h_v284 h_v285 (by ns_tac) (by ns_tac) as ⟨v286, s281, hinv281, h_v286⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 dropping h_v284 h_v285 hinv280 s280 v284 v285
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s281 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv281 h64 as ⟨v287, s282, hinv282, h_v287⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v286 dropping hinv281 s281
  store_step with Store.apply_rep s282 v286 v287 _ _ hinv282 h64 h_v286 h_v287 (by ns_tac) (by ns_tac) as ⟨v288, s283, hinv283, h_v288⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 dropping h_v286 h_v287 hinv282 s282 v286 v287
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s283 0#u32 (0) (by scalar_tac) hinv283 h64 as ⟨v289, s284, hinv284, h_v289⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 dropping hinv283 s283
  step as ⟨e_v290, he_v290⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s284 e_v290 (by rw [he_v290]; exact empty_args) hinv284 h64 as ⟨v290, s285, hinv285, h_v290⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 dropping he_v290 hinv284 e_v290 s284
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s285 1#u32 (1) (by scalar_tac) hinv285 h64 as ⟨v291, s286, hinv286, h_v291⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 dropping hinv285 s285
  step as ⟨e_v292, he_v292⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s286 e_v292 (by rw [he_v292]; exact empty_args) hinv286 h64 as ⟨v292, s287, hinv287, h_v292⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v291 dropping he_v292 hinv286 e_v292 s286
  step as ⟨e_v293, he_v293⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s287 e_v293 (by rw [he_v293]; rfl) h_v292 h_a0 hinv287 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v293, s288, hinv288, h_v293⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v291 dropping h_v292 he_v293 hinv287 e_v293 s287 v292
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s288 v291 v293 a0 _ _ _ hinv288 h64 (hG.rem hrem) h_v291 h_v293 h_a0 as ⟨v294, s289, hinv289, h_v294⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 dropping h_v291 h_v293 hinv288 s288 v291 v293
  step as ⟨e_v295, he_v295⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s289 e_v295 (by rw [he_v295]; exact empty_args) hinv289 h64 as ⟨v295, s290, hinv290, h_v295⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v294 dropping he_v295 hinv289 e_v295 s289
  store_step with Store.literal_boolean_spec s290 false hinv290 h64 as ⟨v296, s291, hinv291, h_v296⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v294 h_v295 dropping hinv290 s290
  store_step with Store.apply_rep s291 v295 v296 _ _ hinv291 h64 h_v295 h_v296 (by ns_tac) (by ns_tac) as ⟨v297, s292, hinv292, h_v297⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v294 dropping h_v295 h_v296 hinv291 s291 v295 v296
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s292 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv292 h64 as ⟨v298, s293, hinv293, h_v298⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v294 h_v297 dropping hinv292 s292
  store_step with Store.apply_rep s293 v297 v298 _ _ hinv293 h64 h_v297 h_v298 (by ns_tac) (by ns_tac) as ⟨v299, s294, hinv294, h_v299⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 h_v294 dropping h_v297 h_v298 hinv293 s293 v297 v298
  store_step with ih.eo__24bv_5fbitblast_5fconcat s294 v294 v299 _ _ hinv294 h64 (hG.rem hrem) h_v294 h_v299 as ⟨v300, s295, hinv295, h_v300⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 dropping h_v294 h_v299 hinv294 s294 v294 v299
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s295 v300 a1 a2 v2 _ _ _ _ hinv295 h64 (hG.rem hrem) h_v300 h_a1 h_a2 h_v2 as ⟨v301, s296, hinv296, h_v301⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 dropping h_v300 hinv295 s295 v300
  store_step with ih.eo__24pair_5fsecond s296 v301 _ hinv296 h64 (hG.rem hrem) h_v301 as ⟨v302, s297, hinv297, h_v302⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v290 dropping h_v301 hinv296 s296 v301
  step as ⟨e_v303, he_v303⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s297 e_v303 (by rw [he_v303]; rfl) h_v290 h_v302 hinv297 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v303, s298, hinv298, h_v303⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 dropping h_v290 h_v302 he_v303 hinv297 e_v303 s297 v290 v302
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s298 1#u32 (-1) (by scalar_tac) hinv298 h64 as ⟨v304, s299, hinv299, h_v304⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v303 dropping hinv298 s298
  step as ⟨e_v305, he_v305⟩
  store_step with Store.builtin_spec_add s299 e_v305 (by rw [he_v305]; rfl) h_v303 h_v304 hinv299 h64 as ⟨v305, s300, hinv300, h_v305⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 dropping h_v303 h_v304 he_v305 hinv299 e_v305 s299 v303 v304
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s300 1#u32 (-1) (by scalar_tac) hinv300 h64 as ⟨v306, s301, hinv301, h_v306⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v305 dropping hinv300 s300
  step as ⟨e_v307, he_v307⟩
  store_step with Store.builtin_spec_add s301 e_v307 (by rw [he_v307]; rfl) h_v305 h_v306 hinv301 h64 as ⟨v307, s302, hinv302, h_v307⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 dropping h_v305 h_v306 he_v307 hinv301 e_v307 s301 v305 v306
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s302 1#u32 (1) (by scalar_tac) hinv302 h64 as ⟨v308, s303, hinv303, h_v308⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 dropping hinv302 s302
  step as ⟨e_v309, he_v309⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s303 e_v309 (by rw [he_v309]; exact empty_args) hinv303 h64 as ⟨v309, s304, hinv304, h_v309⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v308 dropping he_v309 hinv303 e_v309 s303
  step as ⟨e_v310, he_v310⟩
  store_step with Store.builtin_spec_list_len n ih.eo__24eo_5fis_5flist_5fnil s304 e_v310 (by rw [he_v310]; rfl) h_v309 h_a0 hinv304 h64 (hG.rem hrem) op_not_left_eo__40from_5fbools as ⟨v310, s305, hinv305, h_v310⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v308 dropping h_v309 he_v310 hinv304 e_v310 s304 v309
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s305 v308 v310 a0 _ _ _ hinv305 h64 (hG.rem hrem) h_v308 h_v310 h_a0 as ⟨v311, s306, hinv306, h_v311⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 dropping h_v308 h_v310 hinv305 s305 v308 v310
  step as ⟨e_v312, he_v312⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s306 e_v312 (by rw [he_v312]; exact empty_args) hinv306 h64 as ⟨v312, s307, hinv307, h_v312⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v311 dropping he_v312 hinv306 e_v312 s306
  store_step with Store.literal_boolean_spec s307 false hinv307 h64 as ⟨v313, s308, hinv308, h_v313⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v311 h_v312 dropping hinv307 s307
  store_step with Store.apply_rep s308 v312 v313 _ _ hinv308 h64 h_v312 h_v313 (by ns_tac) (by ns_tac) as ⟨v314, s309, hinv309, h_v314⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v311 dropping h_v312 h_v313 hinv308 s308 v312 v313
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s309 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv309 h64 as ⟨v315, s310, hinv310, h_v315⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v311 h_v314 dropping hinv309 s309
  store_step with Store.apply_rep s310 v314 v315 _ _ hinv310 h64 h_v314 h_v315 (by ns_tac) (by ns_tac) as ⟨v316, s311, hinv311, h_v316⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 h_v311 dropping h_v314 h_v315 hinv310 s310 v314 v315
  store_step with ih.eo__24bv_5fbitblast_5fconcat s311 v311 v316 _ _ hinv311 h64 (hG.rem hrem) h_v311 h_v316 as ⟨v317, s312, hinv312, h_v317⟩ growing hG carrying h_a0 h_a1 h_a2 h_v2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 dropping h_v311 h_v316 hinv311 s311 v311 v316
  store_step with ih.eo__24bv_5fdiv_5fmod_5fimpl s312 v317 a1 a2 v2 _ _ _ _ hinv312 h64 (hG.rem hrem) h_v317 h_a1 h_a2 h_v2 as ⟨v318, s313, hinv313, h_v318⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 dropping h_v2 h_v317 hinv312 s312 v2 v317
  store_step with ih.eo__24pair_5fsecond s313 v318 _ hinv313 h64 (hG.rem hrem) h_v318 as ⟨v319, s314, hinv314, h_v319⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v288 h_v289 h_v307 dropping h_v318 hinv313 s313 v318
  store_step with ih.eo__24bv_5fbitblast_5fsubsequence s314 v289 v307 v319 _ _ _ hinv314 h64 (hG.rem hrem) h_v289 h_v307 h_v319 as ⟨v320, s315, hinv315, h_v320⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v288 dropping h_v289 h_v307 h_v319 hinv314 s314 v289 v307 v319
  store_step with ih.eo__24bv_5fbitblast_5fconcat s315 v288 v320 _ _ hinv315 h64 (hG.rem hrem) h_v288 h_v320 as ⟨v321, s316, hinv316, h_v321⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 dropping h_v288 h_v320 hinv315 s315 v288 v320
  step as ⟨e_v322, he_v322⟩
  store_step with CtorSpec.eo_ite.construct s316 e_v322 (by rw [he_v322]; exact empty_args) hinv316 h64 as ⟨v322, s317, hinv317, h_v322⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 dropping he_v322 hinv316 e_v322 s316
  step as ⟨e_v323, he_v323⟩
  store_step with CtorSpec.eo__3d.construct s317 e_v323 (by rw [he_v323]; exact empty_args) hinv317 h64 as ⟨v323, s318, hinv318, h_v323⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v322 dropping he_v323 hinv317 e_v323 s317
  store_step with ih.eo__24bv_5fbitblast_5fhead s318 a0 _ hinv318 h64 (hG.rem hrem) h_a0 as ⟨v324, s319, hinv319, h_v324⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v322 h_v323 dropping hinv318 s318
  store_step with Store.apply_mk_rep s319 v323 v324 _ _ hinv319 h64 h_v323 h_v324 as ⟨v325, s320, hinv320, h_v325⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v322 dropping h_v323 h_v324 hinv319 s319 v323 v324
  store_step with Store.literal_boolean_spec s320 true hinv320 h64 as ⟨v326, s321, hinv321, h_v326⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v322 h_v325 dropping hinv320 s320
  store_step with Store.apply_mk_rep s321 v325 v326 _ _ hinv321 h64 h_v325 h_v326 as ⟨v327, s322, hinv322, h_v327⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v322 dropping h_v325 h_v326 hinv321 s321 v325 v326
  store_step with Store.apply_mk_rep s322 v322 v327 _ _ hinv322 h64 h_v322 h_v327 as ⟨v328, s323, hinv323, h_v328⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 dropping h_v322 h_v327 hinv322 s322 v322 v327
  store_step with Store.literal_boolean_spec s323 true hinv323 h64 as ⟨v329, s324, hinv324, h_v329⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v328 dropping hinv323 s323
  store_step with Store.apply_mk_rep s324 v328 v329 _ _ hinv324 h64 h_v328 h_v329 as ⟨v330, s325, hinv325, h_v330⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 dropping h_v328 h_v329 hinv324 s324 v328 v329
  store_step with Store.literal_boolean_spec s325 false hinv325 h64 as ⟨v331, s326, hinv326, h_v331⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v330 dropping hinv325 s325
  store_step with Store.apply_mk_rep s326 v330 v331 _ _ hinv326 h64 h_v330 h_v331 as ⟨v332, s327, hinv327, h_v332⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 dropping h_v330 h_v331 hinv326 s326 v330 v331
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s327 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv327 h64 as ⟨v333, s328, hinv328, h_v333⟩ growing hG carrying h_a0 h_a1 h_a2 h_v163 h_v171 h_v231 h_v283 h_v321 h_v332 dropping hinv327 s327
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s328 v321 a2 v332 v333 _ _ _ _ hinv328 h64 (hG.rem hrem) h_v321 h_a2 h_v332 h_v333 as ⟨v334, s329, hinv329, h_v334⟩ growing hG carrying h_a0 h_a1 h_v163 h_v171 h_v231 h_v283 dropping h_a2 h_v321 h_v332 h_v333 hinv328 s328 v321 v332 v333
  store_step with ih.eo__24pair_5fsecond s329 v334 _ hinv329 h64 (hG.rem hrem) h_v334 as ⟨v335, s330, hinv330, h_v335⟩ growing hG carrying h_a0 h_a1 h_v163 h_v171 h_v231 h_v283 dropping h_v334 hinv329 s329 v334
  step as ⟨e_v336, he_v336⟩
  store_step with CtorSpec.eo_not.construct s330 e_v336 (by rw [he_v336]; exact empty_args) hinv330 h64 as ⟨v336, s331, hinv331, h_v336⟩ growing hG carrying h_a0 h_a1 h_v163 h_v171 h_v231 h_v283 h_v335 dropping he_v336 hinv330 e_v336 s330
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s331 v336 a1 _ _ hinv331 h64 (hG.rem hrem) h_v336 h_a1 as ⟨v337, s332, hinv332, h_v337⟩ growing hG carrying h_a0 h_v163 h_v171 h_v231 h_v283 h_v335 dropping h_a1 h_v336 hinv331 s331 v336
  store_step with Store.literal_boolean_spec s332 true hinv332 h64 as ⟨v338, s333, hinv333, h_v338⟩ growing hG carrying h_a0 h_v163 h_v171 h_v231 h_v283 h_v335 h_v337 dropping hinv332 s332
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s333 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv333 h64 as ⟨v339, s334, hinv334, h_v339⟩ growing hG carrying h_a0 h_v163 h_v171 h_v231 h_v283 h_v335 h_v337 h_v338 dropping hinv333 s333
  store_step with ih.eo__24bv_5fripple_5fcarry_5fadder_5f2 s334 v335 v337 v338 v339 _ _ _ _ hinv334 h64 (hG.rem hrem) h_v335 h_v337 h_v338 h_v339 as ⟨v340, s335, hinv335, h_v340⟩ growing hG carrying h_a0 h_v163 h_v171 h_v231 h_v283 dropping h_v335 h_v337 h_v338 h_v339 hinv334 s334 v335 v337 v338 v339
  store_step with ih.eo__24pair_5fsecond s335 v340 _ hinv335 h64 (hG.rem hrem) h_v340 as ⟨v341, s336, hinv336, h_v341⟩ growing hG carrying h_a0 h_v163 h_v171 h_v231 h_v283 dropping h_v340 hinv335 s335 v340
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fite s336 v231 v283 v341 _ _ _ hinv336 h64 (hG.rem hrem) h_v231 h_v283 h_v341 as ⟨v342, s337, hinv337, h_v342⟩ growing hG carrying h_a0 h_v163 h_v171 dropping h_v231 h_v283 h_v341 hinv336 s336 v231 v283 v341
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fite s337 v171 a0 v342 _ _ _ hinv337 h64 (hG.rem hrem) h_v171 h_a0 h_v342 as ⟨v343, s338, hinv338, h_v343⟩ growing hG carrying h_v163 dropping h_a0 h_v171 h_v342 hinv337 s337 v171 v342
  store_step with Store.apply_mk_rep s338 v163 v343 _ _ hinv338 h64 h_v163 h_v343 as ⟨v344, s339, hinv339, h_v344⟩ growing hG carrying dropping h_v163 h_v343 hinv338 s338 v163 v343
  case_done hinv339 hG with h_v344 in EoCases.__bv_div_mod_impl.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's fall-through helpers of `__bv_div_mod_impl`, each the program's cases from its first on. -/
theorem eo__24bv_5fdiv_5fmod_5fimpl.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___bv_div_mod_impl x_a0 x_a1 x_a2 x_a3 =
      firstSome [EoCases.__bv_div_mod_impl.case_2 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___bv_div_mod_impl
  unfold EoCases.__bv_div_mod_impl.case_2
  logos_eq_deep

/-- logos's `__bv_div_mod_impl` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fdiv_5fmod_5fimpl.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __bv_div_mod_impl x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_div_mod_impl.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__bv_div_mod_impl.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__bv_div_mod_impl.case_2 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __bv_div_mod_impl
  unfold EoCases.__bv_div_mod_impl.case_0 EoCases.__bv_div_mod_impl.case_1
  have hn := eo__24bv_5fdiv_5fmod_5fimpl.helper_1
  logos_eq_deep

theorem body_eo__24bv_5fdiv_5fmod_5fimpl_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24bv_5fdiv_5fmod_5fimpl s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_div_mod_impl x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fdiv_5fmod_5fimpl.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24bv_5fdiv_5fmod_5fimpl
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24bv_5fdiv_5fmod_5fimpl_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  case_step with case_1_eo__24bv_5fdiv_5fmod_5fimpl_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3 hc0
  case_step with case_2_eo__24bv_5fdiv_5fmod_5fimpl_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 hc1 hc2 in EoCases.__bv_div_mod_impl.case_0 EoCases.__bv_div_mod_impl.case_1 EoCases.__bv_div_mod_impl.case_2

theorem eo__24bv_5fdiv_5fmod_5fimpl_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fdiv_5fmod_5fimpl.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24bv_5fdiv_5fmod_5fimpl
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 31#u32 _ [a0, a1, a2, a3] rfl
    (fun s1 => body_eo__24bv_5fdiv_5fmod_5fimpl s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__bv_div_mod_impl x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, y0, y1, y2, y3, hargs, hb0, hb1, hb2, hb3, hr⟩ := ProgramSem.of_31 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_31 ⟨a0, a1, a2, a3, x_a0, x_a1, x_a2, x_a3, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fdiv_5fmod_5fimpl_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
