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

set_option maxHeartbeats 20000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) (hn_a5 : x_a5 ≠ Eo.Term.Stuck) (hn_a6 : x_a6 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_concat_extract_merge.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_concat_extract_merge.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v4 h_v6 h_v7 dropping h_a7 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_same v7 a5 with h_v7 h_a5 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_same v14 a4 with h_v14 h_a4 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__2b.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v18 h_v20 h_v21 dropping h_v11 h_v13 h_v14 h_v15 h_v17 he_v22 hinv2 e_v22 s2 v11 v13 v14 v15 v17
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v18 h_v21 dropping h_v20 h_v22 hinv3 s3 v20 v22
  pat_same v21 v23 with h_v21 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v18 dropping h_v21 h_v23 hinv4 s4 v21 v23
  pat_same v18 v24 with h_v18 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_concat_extract_merge.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v25 (by rw [he_v25]; exact empty_args) hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 dropping h_v18 h_v24 he_v25 hinv5 e_v25 s5 v18 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_concat.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v25 dropping he_v26 hinv6 e_v26 s6
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_concat.construct s7 e_v27 (by rw [he_v27]; exact empty_args) hinv7 h64 as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_v25 h_v26 dropping he_v27 hinv7 e_v27 s7
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_extract.construct s8 e_v28 (by rw [he_v28]; rfl) h_a6 h_a5 hinv8 h64 as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v25 h_v26 h_v27 dropping h_a5 he_v28 hinv8 e_v28 s8
  store_step with Store.apply_rep s9 v28 a1 _ _ hinv9 h64 h_v28 h_a1 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v25 h_v26 h_v27 dropping h_v28 hinv9 s9 v28
  store_step with Store.apply_rep s10 v27 v29 _ _ hinv10 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v25 h_v26 dropping h_v27 h_v29 hinv10 s10 v27 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_concat.construct s11 e_v31 (by rw [he_v31]; exact empty_args) hinv11 h64 as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v25 h_v26 h_v30 dropping he_v31 hinv11 e_v31 s11
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_extract.construct s12 e_v32 (by rw [he_v32]; rfl) h_a4 h_a3 hinv12 h64 as ⟨v32, s13, hinv13, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v26 h_v30 h_v31 dropping h_a4 he_v32 hinv12 e_v32 s12
  store_step with Store.apply_rep s13 v32 a1 _ _ hinv13 h64 h_v32 h_a1 (by ns_tac) (by ns_tac) as ⟨v33, s14, hinv14, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v26 h_v30 h_v31 dropping h_v32 hinv13 s13 v32
  store_step with Store.apply_rep s14 v31 v33 _ _ hinv14 h64 h_v31 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s15, hinv15, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v26 h_v30 dropping h_v31 h_v33 hinv14 s14 v31 v33
  store_step with Store.apply_rep s15 v34 a2 _ _ hinv15 h64 h_v34 h_a2 (by ns_tac) (by ns_tac) as ⟨v35, s16, hinv16, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v26 h_v30 dropping h_v34 hinv15 s15 v34
  store_step with Store.apply_rep s16 v30 v35 _ _ hinv16 h64 h_v30 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s17, hinv17, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v26 dropping h_v30 h_v35 hinv16 s16 v30 v35
  step as ⟨e_v37, he_v37⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s17 e_v37 (by rw [he_v37]; rfl) h_v26 h_a0 h_v36 hinv17 h64 (hG.rem hrem) op_not_left_eo_concat op_unique_nil_eo_concat as ⟨v37, s18, hinv18, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 dropping h_v26 h_v36 he_v37 hinv17 e_v37 s17 v26 v36
  store_step with Store.apply_mk_rep s18 v25 v37 _ _ hinv18 h64 h_v25 h_v37 as ⟨v38, s19, hinv19, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 dropping h_v25 h_v37 hinv18 s18 v25 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_concat.construct s19 e_v39 (by rw [he_v39]; exact empty_args) hinv19 h64 as ⟨v39, s20, hinv20, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v38 dropping he_v39 hinv19 e_v39 s19
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_concat.construct s20 e_v40 (by rw [he_v40]; exact empty_args) hinv20 h64 as ⟨v40, s21, hinv21, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v38 h_v39 dropping he_v40 hinv20 e_v40 s20
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_concat.construct s21 e_v41 (by rw [he_v41]; exact empty_args) hinv21 h64 as ⟨v41, s22, hinv22, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v38 h_v39 h_v40 dropping he_v41 hinv21 e_v41 s21
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_extract.construct s22 e_v42 (by rw [he_v42]; rfl) h_a6 h_a3 hinv22 h64 as ⟨v42, s23, hinv23, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v38 h_v39 h_v40 h_v41 dropping h_a3 h_a6 he_v42 hinv22 e_v42 s22
  store_step with Store.apply_rep s23 v42 a1 _ _ hinv23 h64 h_v42 h_a1 (by ns_tac) (by ns_tac) as ⟨v43, s24, hinv24, h_v43⟩ growing hG carrying h_a0 h_a2 h_v38 h_v39 h_v40 h_v41 dropping h_a1 h_v42 hinv23 s23 v42
  store_step with Store.apply_rep s24 v41 v43 _ _ hinv24 h64 h_v41 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s25, hinv25, h_v44⟩ growing hG carrying h_a0 h_a2 h_v38 h_v39 h_v40 dropping h_v41 h_v43 hinv24 s24 v41 v43
  store_step with Store.apply_rep s25 v44 a2 _ _ hinv25 h64 h_v44 h_a2 (by ns_tac) (by ns_tac) as ⟨v45, s26, hinv26, h_v45⟩ growing hG carrying h_a0 h_v38 h_v39 h_v40 dropping h_a2 h_v44 hinv25 s25 v44
  step as ⟨e_v46, he_v46⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s26 e_v46 (by rw [he_v46]; rfl) h_v40 h_a0 h_v45 hinv26 h64 (hG.rem hrem) op_not_left_eo_concat op_unique_nil_eo_concat as ⟨v46, s27, hinv27, h_v46⟩ growing hG carrying h_v38 h_v39 dropping h_a0 h_v40 h_v45 he_v46 hinv26 e_v46 s26 v40 v45
  step as ⟨e_v47, he_v47⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s27 e_v47 (by rw [he_v47]; rfl) h_v39 h_v46 hinv27 h64 (hG.rem hrem) op_not_left_eo_concat op_nil_apply_eo_concat as ⟨v47, s28, hinv28, h_v47⟩ growing hG carrying h_v38 dropping h_v39 h_v46 he_v47 hinv27 e_v47 s27 v39 v46
  store_step with Store.apply_mk_rep s28 v38 v47 _ _ hinv28 h64 h_v38 h_v47 as ⟨v48, s29, hinv29, h_v48⟩ growing hG carrying dropping h_v38 h_v47 hinv28 s28 v38 v47
  case_done hinv29 hG with h_v48 in EoCases.__eo_prog_bv_concat_extract_merge.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_bv_concat_extract_merge` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_bv_concat_extract_merge x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else if x_a5 = Eo.Term.Stuck then HasStuck.stuck else if x_a6 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_concat_extract_merge.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_concat_extract_merge
  unfold EoCases.__eo_prog_bv_concat_extract_merge.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_concat_extract_merge x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  stuck_check h_a5 : x_a5 as hn_a5 else hinv hG
  stuck_check h_a6 : x_a6 as hn_a6 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_a5 hn_a6 hc0 in EoCases.__eo_prog_bv_concat_extract_merge.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_bv_concat_extract_merge x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
