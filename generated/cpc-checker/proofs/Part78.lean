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
theorem case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v2 h_v4 h_v5 dropping h_a2 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_a4 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v5 h_v9 h_v11 h_v12 dropping h_a4 h_v4 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v12 as ⟨v15, v16, x_v15, x_v16, h_v15, h_v16, hn_v15, hn_v16⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_unapply h_v15 as ⟨v18, v19, x_v18, x_v19, h_v18, h_v19, hn_v18, hn_v19⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v20 (by rw [he_v20]; exact empty_args) hinv2 h64 as ⟨v20, s3, hinv3, h_v20⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v5 h_v9 h_v16 h_v18 h_v19 dropping h_v11 h_v12 h_v13 h_v15 he_v20 hinv2 e_v20 s2 v11 v12 v13 v15
  pat_same v18 v20 with h_v18 h_v20 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_0
  pat_same v19 v5 with h_v19 h_v5 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v5 h_v9 h_v16 dropping h_v18 h_v19 h_v20 he_v21 hinv3 e_v21 s3 v18 v19 v20
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s4 e_v22 (by rw [he_v22]; rfl) h_v21 h_v16 h_v5 hinv4 h64 (hG.rem hrem) (by not_left_tac) as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 h_v16 dropping h_v21 h_v5 he_v22 hinv4 e_v22 s4 v21 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s5 1#u32 (-1) (by scalar_tac) hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 h_v16 h_v22 dropping hinv5 s5
  have h_req_v28 := (show requires_0_eo__24is_5fquant_5fdt_5fsplit_5fconj s6 v22 v23 v16 v9 a0 a1 v2 a3 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v22 v23 with h_v22 h_v23 using hinv6 hG
    req_stuck h_v22 as hq_v22 using hinv6 hG
    step as ⟨e_v24, he_v24⟩
    store_step with CtorSpec.eo_forall.construct s6 e_v24 (by rw [he_v24]; exact empty_args) hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 h_v16 dropping h_v22 h_v23 he_v24 hinv6 e_v24 s6 v22 v23
    store_step with Store.apply_rep s7 v24 v16 _ _ hinv7 h64 h_v24 h_v16 (by ns_tac) (by ns_tac) as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 h_v9 dropping h_v16 h_v24 hinv7 s7 v16 v24
    store_step with Store.apply_rep s8 v25 v9 _ _ hinv8 h64 h_v25 h_v9 (by ns_tac) (by ns_tac) as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_a0 h_a1 h_a3 h_v2 dropping h_v25 h_v9 hinv8 s8 v25 v9
    store_step with ih.eo__24is_5fquant_5fdt_5fsplit_5fconj s9 a0 a1 v2 a3 v26 _ _ _ _ _ hinv9 h64 (hG.rem hrem) h_a0 h_a1 h_v2 h_a3 h_v26 as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying dropping h_a0 h_a1 h_a3 h_v2 h_v26 hinv9 s9 v2 v26
    req_done hinv10 hG with h_v27 using hq_v22)
  store_step with h_req_v28 as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying dropping h_req_v28 h_v16 h_v2 h_v22 h_v23 h_v9 hinv6 s6 v16 v2 v22 v23 v9
  case_done hinv11 hG with h_v28 in EoCases.__is_quant_dt_split_conj.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12 hn_v15 hn_v16 hn_v18 hn_v19

set_option maxHeartbeats 4000000 in
theorem case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_a4 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v5 h_v6 dropping h_a2 h_a4 h_v0 h_v2 he_v7 hinv1 e_v7 s1 v0 v2
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_1
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v12 h_v13 dropping h_v5 h_v6 h_v7 h_v9 he_v14 hinv2 e_v14 s2 v5 v6 v7 v9
  pat_same v12 v14 with h_v12 h_v14 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_1
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v12 h_v14 he_v15 hinv3 e_v15 s3 v12 v14
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_list_find n ih.eo__24eo_5fis_5flist_5fnil s4 e_v16 (by rw [he_v16]; rfl) h_v15 h_v10 h_v13 hinv4 h64 (hG.rem hrem) (by not_left_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v15 he_v16 hinv4 e_v16 s4 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s5 1#u32 (-1) (by scalar_tac) hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v16 dropping hinv5 s5
  have h_req_v32 := (show requires_3_eo__24is_5fquant_5fdt_5fsplit_5fconj s6 v16 v17 v13 a3 a1 v10 v3 a0 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_3_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    req_same v16 v17 with h_v16 h_v17 using hinv6 hG
    req_stuck h_v16 as hq_v16 using hinv6 hG
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s6 e_v18 (by rw [he_v18]; exact empty_args) hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v16 h_v17 he_v18 hinv6 e_v18 s6 v16 v17
    store_step with Store.apply_rep s7 v18 v13 _ _ hinv7 h64 h_v18 h_v13 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v18 hinv7 s7 v18
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v19 dropping he_v20 hinv8 e_v20 s8
    store_step with Store.apply_rep s9 v19 v20 _ _ hinv9 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v19 h_v20 hinv9 s9 v19 v20
    step as ⟨e_v22, he_v22⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s10 e_v22 (by rw [he_v22]; exact empty_args) hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v21 dropping he_v22 hinv10 e_v22 s10
    store_step with ih.eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec s11 a3 v21 v22 _ _ _ hinv11 h64 (hG.rem hrem) h_a3 h_v21 h_v22 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 dropping h_v21 h_v22 hinv11 s11 v21 v22
    store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v10 h_v13 h_v23 dropping hinv12 s12
    have h_req_v31 := (show requires_2_eo__24is_5fquant_5fdt_5fsplit_5fconj s13 v23 v24 a1 v13 v10 v3 a0 a3 ⦃ r s' => s'.Inv ∧ s13.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
      unfold requires_2_eo__24is_5fquant_5fdt_5fsplit_5fconj
      have hrem := (hG.rem hrem)
      have hG := Store.Grows.refl s13
      req_same v23 v24 with h_v23 h_v24 using hinv13 hG
      req_stuck h_v23 as hq_v23 using hinv13 hG
      store_step with Store.apply_rep s13 a1 v13 _ _ hinv13 h64 h_a1 h_v13 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a3 h_v3 h_v10 dropping h_a1 h_v13 h_v23 h_v24 hinv13 s13 v13 v23 v24
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s14 e_v26 (by rw [he_v26]; exact empty_args) hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_a0 h_a3 h_v3 h_v10 h_v25 dropping he_v26 hinv14 e_v26 s14
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo_forall.construct s15 e_v27 (by rw [he_v27]; exact empty_args) hinv15 h64 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_a0 h_a3 h_v3 h_v10 h_v25 h_v26 dropping he_v27 hinv15 e_v27 s15
      store_step with Store.apply_rep s16 v27 v10 _ _ hinv16 h64 h_v27 h_v10 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_a0 h_a3 h_v3 h_v25 h_v26 dropping h_v10 h_v27 hinv16 s16 v10 v27
      store_step with Store.apply_rep s17 v28 v3 _ _ hinv17 h64 h_v28 h_v3 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_a3 h_v25 h_v26 dropping h_v28 h_v3 hinv17 s17 v28 v3
      store_step with ih.eo__24is_5fquant_5fdt_5fsplit_5fconj s18 a0 v25 v26 a3 v29 _ _ _ _ _ hinv18 h64 (hG.rem hrem) h_a0 h_v25 h_v26 h_a3 h_v29 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying dropping h_a0 h_a3 h_v25 h_v26 h_v29 hinv18 s18 v25 v26 v29
      req_done hinv19 hG with h_v30 using hq_v23)
    store_step with h_req_v31 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying dropping h_a3 h_req_v31 h_v10 h_v13 h_v23 h_v24 h_v3 hinv13 s13 v10 v13 v23 v24 v3
    req_done hinv20 hG with h_v31 using hq_v16)
  store_step with h_req_v32 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying dropping h_req_v32 h_v10 h_v13 h_v16 h_v17 h_v3 hinv6 s6 v10 v13 v16 v17 v3
  case_done hinv21 hG with h_v32 in EoCases.__is_quant_dt_split_conj.case_1 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v2 hn_v3 hn_v5 hn_v6 hn_v9 hn_v10 hn_v12 hn_v13

set_option maxHeartbeats 4000000 in
theorem case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_2
  pat_unapply h_a4 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_2
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_forall.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v5 h_v6 dropping h_a2 h_a4 h_v0 h_v2 he_v7 hinv1 e_v7 s1 v0 v2
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__is_quant_dt_split_conj.case_2
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v6 dropping h_v5 h_v7 he_v8 hinv2 e_v8 s2 v5 v7
  pat_same v6 v8 with h_v6 h_v8 using hinv3 else hinv3 hG in EoCases.__is_quant_dt_split_conj.case_2
  store_step with ih.eo__24eo_5ftypeof s3 a1 _ hinv3 h64 (hG.rem hrem) h_a1 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 dropping h_v6 h_v8 hinv3 s3 v6 v8
  store_step with ih.eo__24eo_5ftypeof s4 a0 _ hinv4 h64 (hG.rem hrem) h_a0 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v9 dropping hinv4 s4
  have h_req_v23 := (show requires_5_eo__24is_5fquant_5fdt_5fsplit_5fconj s5 v9 v10 a0 a1 a3 v3 ⦃ r s' => s'.Inv ∧ s5.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_5_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s5
    req_same v9 v10 with h_v9 h_v10 using hinv5 hG
    req_stuck h_v9 as hq_v9 using hinv5 hG
    store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 dropping h_v10 h_v9 hinv5 s5 v10 v9
    step as ⟨e_v12, he_v12⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a3 h_v3 h_v11 dropping he_v12 hinv6 e_v12 s6
    store_step with Store.apply_rep s7 v12 a0 _ _ hinv7 h64 h_v12 h_a0 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 dropping h_a0 h_v12 hinv7 s7 v12
    step as ⟨e_v14, he_v14⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 h_v13 dropping he_v14 hinv8 e_v14 s8
    store_step with Store.apply_rep s9 v13 v14 _ _ hinv9 h64 h_v13 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 dropping h_v13 h_v14 hinv9 s9 v13 v14
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a1 h_a3 h_v3 h_v11 h_v15 dropping he_v16 hinv10 e_v16 s10
    store_step with Store.apply_rep s11 v16 a1 _ _ hinv11 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 dropping h_a1 h_v16 hinv11 s11 v16
    step as ⟨e_v18, he_v18⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 h_v17 dropping he_v18 hinv12 e_v18 s12
    store_step with Store.apply_rep s13 v17 v18 _ _ hinv13 h64 h_v17 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 dropping h_v17 h_v18 hinv13 s13 v17 v18
    step as ⟨e_v20, he_v20⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a3 h_v3 h_v11 h_v15 h_v19 dropping he_v20 hinv14 e_v20 s14
    store_step with ih.eo__24substitute_5fsimul_5frec s15 v11 a3 v15 v19 v20 _ _ _ _ _ hinv15 h64 (hG.rem hrem) h_v11 h_a3 h_v15 h_v19 h_v20 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v3 dropping h_a3 h_v11 h_v15 h_v19 h_v20 hinv15 s15 v11 v15 v19 v20
    step as ⟨e_v22, he_v22⟩
    store_step with Store.builtin_spec_eq s16 e_v22 (by rw [he_v22]; rfl) h_v21 h_v3 hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying dropping h_v21 h_v3 he_v22 hinv16 e_v22 s16 v21 v3
    req_done hinv17 hG with h_v22 using hq_v9)
  store_step with h_req_v23 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying dropping h_a0 h_a1 h_req_v23 h_v10 h_v3 h_v9 hinv5 s5 v10 v3 v9
  case_done hinv18 hG with h_v23 in EoCases.__is_quant_dt_split_conj.case_2 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v2 hn_v3 hn_v5 hn_v6

set_option maxHeartbeats 4000000 in
theorem case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__is_quant_dt_split_conj.case_3
  store_step with ih.eo__24eo_5ftypeof s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 dropping h_a2 h_v0 hinv1 s1 v0
  store_step with ih.eo__24eo_5ftypeof s2 a0 _ hinv2 h64 (hG.rem hrem) h_a0 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v1 dropping hinv2 s2
  have h_req_v15 := (show requires_6_eo__24is_5fquant_5fdt_5fsplit_5fconj s3 v1 v2 a0 a1 a3 a4 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_6_eo__24is_5fquant_5fdt_5fsplit_5fconj
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    req_same v1 v2 with h_v1 h_v2 using hinv3 hG
    req_stuck h_v1 as hq_v1 using hinv3 hG
    store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 dropping h_v1 h_v2 hinv3 s3 v1 v2
    step as ⟨e_v4, he_v4⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v3 dropping he_v4 hinv4 e_v4 s4
    store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 dropping h_a0 h_v4 hinv5 s5 v4
    step as ⟨e_v6, he_v6⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 h_v5 dropping he_v6 hinv6 e_v6 s6
    store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 dropping h_v5 h_v6 hinv7 s7 v5 v6
    step as ⟨e_v8, he_v8⟩
    store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_a3 h_a4 h_v3 h_v7 dropping he_v8 hinv8 e_v8 s8
    store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 dropping h_a1 h_v8 hinv9 s9 v8
    step as ⟨e_v10, he_v10⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 h_v9 dropping he_v10 hinv10 e_v10 s10
    store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 dropping h_v10 h_v9 hinv11 s11 v10 v9
    step as ⟨e_v12, he_v12⟩
    store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a3 h_a4 h_v3 h_v7 h_v11 dropping he_v12 hinv12 e_v12 s12
    store_step with ih.eo__24substitute_5fsimul_5frec s13 v3 a3 v7 v11 v12 _ _ _ _ _ hinv13 h64 (hG.rem hrem) h_v3 h_a3 h_v7 h_v11 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a4 dropping h_a3 h_v11 h_v12 h_v3 h_v7 hinv13 s13 v11 v12 v3 v7
    step as ⟨e_v14, he_v14⟩
    store_step with Store.builtin_spec_eq s14 e_v14 (by rw [he_v14]; rfl) h_v13 h_a4 hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_a4 h_v13 he_v14 hinv14 e_v14 s14 v13
    req_done hinv15 hG with h_v14 using hq_v1)
  store_step with h_req_v15 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying dropping h_a0 h_a1 h_req_v15 h_v1 h_v2 hinv3 s3 v1 v2
  case_done hinv16 hG with h_v15 in EoCases.__is_quant_dt_split_conj.case_3 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4

set_option maxHeartbeats 4000000 in
/-- logos's fall-through helpers of `__is_quant_dt_split_conj`, each the program's cases from its first on. -/
theorem eo__24is_5fquant_5fdt_5fsplit_5fconj.helper_1 (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4 =
      firstSome [EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___is_quant_dt_split_conj
  unfold EoCases.__is_quant_dt_split_conj.case_1 EoCases.__is_quant_dt_split_conj.case_2 EoCases.__is_quant_dt_split_conj.case_3
  logos_eq_deep

set_option maxHeartbeats 4000000 in
/-- logos's `__is_quant_dt_split_conj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24is_5fquant_5fdt_5fsplit_5fconj.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__is_quant_dt_split_conj.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_1 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_2 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__is_quant_dt_split_conj.case_3 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __is_quant_dt_split_conj
  unfold EoCases.__is_quant_dt_split_conj.case_0
  have hn := eo__24is_5fquant_5fdt_5fsplit_5fconj.helper_1
  logos_eq_deep

set_option maxHeartbeats 4000000 in
theorem body_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24is_5fquant_5fdt_5fsplit_5fconj s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24is_5fquant_5fdt_5fsplit_5fconj.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24is_5fquant_5fdt_5fsplit_5fconj
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  case_step with case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0
  case_step with case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s2 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1
  case_step with case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec n ih s3 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 hc1 hc2 hc3 in EoCases.__is_quant_dt_split_conj.case_0 EoCases.__is_quant_dt_split_conj.case_1 EoCases.__is_quant_dt_split_conj.case_2 EoCases.__is_quant_dt_split_conj.case_3

set_option maxHeartbeats 4000000 in
theorem eo__24is_5fquant_5fdt_5fsplit_5fconj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24is_5fquant_5fdt_5fsplit_5fconj.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24is_5fquant_5fdt_5fsplit_5fconj
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 910#u32 _ [a0, a1, a2, a3, a4] rfl
    (fun s1 => body_eo__24is_5fquant_5fdt_5fsplit_5fconj s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__is_quant_dt_split_conj x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, b3, b4, y0, y1, y2, y3, y4, hargs, hb0, hb1, hb2, hb3, hb4, hr⟩ := ProgramSem.of_910 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      obtain rfl := Rep.functional hb3 (Represents.congr h_a3 hn)
      obtain rfl := Rep.functional hb4 (Represents.congr h_a4 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_910 ⟨a0, a1, a2, a3, a4, x_a0, x_a1, x_a2, x_a3, x_a4, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, Rep.mono hpre h_a3, Rep.mono hpre h_a4, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24is_5fquant_5fdt_5fsplit_5fconj_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
