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

set_option maxHeartbeats 2070000 in
theorem case_0_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2econtains.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__40purify.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2econtains.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  store_step with Store.apply_rep s7 v7 v12 _ _ hinv7 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 dropping h_v12 h_v7 hinv7 s7 v12 v7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v13 dropping he_v14 hinv8 e_v14 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_forall.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 dropping he_v15 hinv9 e_v15 s9
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 dropping he_v16 hinv10 e_v16 s10
  step as ⟨e_v17, he_v17⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s11 _ _ rfl hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 h_v16 dropping hinv11 s11
  replace h_v17 := Represents.rep_of_eq h_v17 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v17]; decide)
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_Int.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 h_v16 h_v17 dropping he_v17 he_v18 hinv12 e_v17 e_v18 s12
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s13 e_v19 (by rw [he_v19]; rfl) h_v17 h_v18 hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 h_v16 dropping h_v17 h_v18 he_v19 hinv13 e_v19 s13 v17 v18
  store_step with Store.apply_rep s14 v16 v19 _ _ hinv14 h64 h_v16 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 dropping h_v16 h_v19 hinv14 s14 v16 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s15 e_v21 (by rw [he_v21]; exact empty_args) hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 h_v20 dropping he_v21 hinv15 e_v21 s15
  store_step with Store.apply_rep s16 v20 v21 _ _ hinv16 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v15 dropping h_v20 h_v21 hinv16 s16 v20 v21
  store_step with Store.apply_rep s17 v15 v22 _ _ hinv17 h64 h_v15 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 dropping h_v15 h_v22 hinv17 s17 v15 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_or.construct s18 e_v24 (by rw [he_v24]; exact empty_args) hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 dropping he_v24 hinv18 e_v24 s18
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_not.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 dropping he_v25 hinv19 e_v25 s19
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3e_3d.construct s20 e_v26 (by rw [he_v26]; exact empty_args) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 dropping he_v26 hinv20 e_v26 s20
  step as ⟨e_v27, he_v27⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s21 _ _ rfl hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 h_v26 dropping hinv21 s21
  replace h_v27 := Represents.rep_of_eq h_v27 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v27]; decide)
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_Int.construct s22 e_v28 (by rw [he_v28]; exact empty_args) hinv22 h64 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 h_v26 h_v27 dropping he_v27 he_v28 hinv22 e_v27 e_v28 s22
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s23 e_v29 (by rw [he_v29]; rfl) h_v27 h_v28 hinv23 h64 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 h_v26 dropping h_v27 h_v28 he_v29 hinv23 e_v29 s23 v27 v28
  store_step with Store.apply_rep s24 v26 v29 _ _ hinv24 h64 h_v26 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 dropping h_v26 h_v29 hinv24 s24 v26 v29
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 h_v30 dropping hinv25 s25
  store_step with Store.apply_rep s26 v30 v31 _ _ hinv26 h64 h_v30 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 h_v25 dropping h_v30 h_v31 hinv26 s26 v30 v31
  store_step with Store.apply_rep s27 v25 v32 _ _ hinv27 h64 h_v25 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v24 dropping h_v25 h_v32 hinv27 s27 v25 v32
  store_step with Store.apply_rep s28 v24 v33 _ _ hinv28 h64 h_v24 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 dropping h_v24 h_v33 hinv28 s28 v24 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_or.construct s29 e_v35 (by rw [he_v35]; exact empty_args) hinv29 h64 as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 dropping he_v35 hinv29 e_v35 s29
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_not.construct s30 e_v36 (by rw [he_v36]; exact empty_args) hinv30 h64 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 dropping he_v36 hinv30 e_v36 s30
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3c_3d.construct s31 e_v37 (by rw [he_v37]; exact empty_args) hinv31 h64 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 dropping he_v37 hinv31 e_v37 s31
  step as ⟨e_v38, he_v38⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s32 _ _ rfl hinv32 h64 as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v37 dropping hinv32 s32
  replace h_v38 := Represents.rep_of_eq h_v38 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v38]; decide)
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_Int.construct s33 e_v39 (by rw [he_v39]; exact empty_args) hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v37 h_v38 dropping he_v38 he_v39 hinv33 e_v38 e_v39 s33
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s34 e_v40 (by rw [he_v40]; rfl) h_v38 h_v39 hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v37 dropping h_v38 h_v39 he_v40 hinv34 e_v40 s34 v38 v39
  store_step with Store.apply_rep s35 v37 v40 _ _ hinv35 h64 h_v37 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 dropping h_v37 h_v40 hinv35 s35 v37 v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__2d.construct s36 e_v42 (by rw [he_v42]; exact empty_args) hinv36 h64 as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 dropping he_v42 hinv36 e_v42 s36
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_str_2elen.construct s37 e_v43 (by rw [he_v43]; exact empty_args) hinv37 h64 as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 h_v42 dropping he_v43 hinv37 e_v43 s37
  store_step with Store.apply_rep s38 v43 v5 _ _ hinv38 h64 h_v43 h_v5 (by ns_tac) (by ns_tac) as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 h_v42 dropping h_v43 hinv38 s38 v43
  store_step with Store.apply_rep s39 v42 v44 _ _ hinv39 h64 h_v42 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 dropping h_v42 h_v44 hinv39 s39 v42 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2elen.construct s40 e_v46 (by rw [he_v46]; exact empty_args) hinv40 h64 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 h_v45 dropping he_v46 hinv40 e_v46 s40
  store_step with Store.apply_rep s41 v46 v2 _ _ hinv41 h64 h_v46 h_v2 (by ns_tac) (by ns_tac) as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 h_v45 dropping h_v46 hinv41 s41 v46
  store_step with Store.apply_rep s42 v45 v47 _ _ hinv42 h64 h_v45 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 h_v41 dropping h_v45 h_v47 hinv42 s42 v45 v47
  store_step with Store.apply_rep s43 v41 v48 _ _ hinv43 h64 h_v41 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 h_v36 dropping h_v41 h_v48 hinv43 s43 v41 v48
  store_step with Store.apply_rep s44 v36 v49 _ _ hinv44 h64 h_v36 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v35 dropping h_v36 h_v49 hinv44 s44 v36 v49
  store_step with Store.apply_rep s45 v35 v50 _ _ hinv45 h64 h_v35 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 dropping h_v35 h_v50 hinv45 s45 v35 v50
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo_or.construct s46 e_v52 (by rw [he_v52]; exact empty_args) hinv46 h64 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v51 dropping he_v52 hinv46 e_v52 s46
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_not.construct s47 e_v53 (by rw [he_v53]; exact empty_args) hinv47 h64 as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 dropping he_v53 hinv47 e_v53 s47
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s48 e_v54 (by rw [he_v54]; exact empty_args) hinv48 h64 as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 dropping he_v54 hinv48 e_v54 s48
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s49 e_v55 (by rw [he_v55]; exact empty_args) hinv49 h64 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_v2 h_v5 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 dropping he_v55 hinv49 e_v55 s49
  store_step with Store.apply_rep s50 v55 v5 _ _ hinv50 h64 h_v55 h_v5 (by ns_tac) (by ns_tac) as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 dropping h_v5 h_v55 hinv50 s50 v5 v55
  step as ⟨e_v57, he_v57⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s51 _ _ rfl hinv51 h64 as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 h_v56 dropping hinv51 s51
  replace h_v57 := Represents.rep_of_eq h_v57 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v57]; decide)
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_Int.construct s52 e_v58 (by rw [he_v58]; exact empty_args) hinv52 h64 as ⟨v58, s53, hinv53, h_v58⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 h_v56 h_v57 dropping he_v57 he_v58 hinv52 e_v57 e_v58 s52
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s53 e_v59 (by rw [he_v59]; rfl) h_v57 h_v58 hinv53 h64 as ⟨v59, s54, hinv54, h_v59⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 h_v56 dropping h_v57 h_v58 he_v59 hinv53 e_v59 s53 v57 v58
  store_step with Store.apply_rep s54 v56 v59 _ _ hinv54 h64 h_v56 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s55, hinv55, h_v60⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 dropping h_v56 h_v59 hinv54 s54 v56 v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_str_2elen.construct s55 e_v61 (by rw [he_v61]; exact empty_args) hinv55 h64 as ⟨v61, s56, hinv56, h_v61⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 h_v60 dropping he_v61 hinv55 e_v61 s55
  store_step with Store.apply_rep s56 v61 v2 _ _ hinv56 h64 h_v61 h_v2 (by ns_tac) (by ns_tac) as ⟨v62, s57, hinv57, h_v62⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 h_v60 dropping h_v61 hinv56 s56 v61
  store_step with Store.apply_rep s57 v60 v62 _ _ hinv57 h64 h_v60 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s58, hinv58, h_v63⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 h_v54 dropping h_v60 h_v62 hinv57 s57 v60 v62
  store_step with Store.apply_rep s58 v54 v63 _ _ hinv58 h64 h_v54 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s59, hinv59, h_v64⟩ growing hG carrying h_v2 h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 dropping h_v54 h_v63 hinv58 s58 v54 v63
  store_step with Store.apply_rep s59 v64 v2 _ _ hinv59 h64 h_v64 h_v2 (by ns_tac) (by ns_tac) as ⟨v65, s60, hinv60, h_v65⟩ growing hG carrying h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 h_v53 dropping h_v2 h_v64 hinv59 s59 v2 v64
  store_step with Store.apply_rep s60 v53 v65 _ _ hinv60 h64 h_v53 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s61, hinv61, h_v66⟩ growing hG carrying h_v13 h_v14 h_v23 h_v34 h_v51 h_v52 dropping h_v53 h_v65 hinv60 s60 v53 v65
  store_step with Store.apply_rep s61 v52 v66 _ _ hinv61 h64 h_v52 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s62, hinv62, h_v67⟩ growing hG carrying h_v13 h_v14 h_v23 h_v34 h_v51 dropping h_v52 h_v66 hinv61 s61 v52 v66
  store_step with Store.literal_boolean_spec s62 false hinv62 h64 as ⟨v68, s63, hinv63, h_v68⟩ growing hG carrying h_v13 h_v14 h_v23 h_v34 h_v51 h_v67 dropping hinv62 s62
  store_step with Store.apply_rep s63 v67 v68 _ _ hinv63 h64 h_v67 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s64, hinv64, h_v69⟩ growing hG carrying h_v13 h_v14 h_v23 h_v34 h_v51 dropping h_v67 h_v68 hinv63 s63 v67 v68
  store_step with Store.apply_rep s64 v51 v69 _ _ hinv64 h64 h_v51 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s65, hinv65, h_v70⟩ growing hG carrying h_v13 h_v14 h_v23 h_v34 dropping h_v51 h_v69 hinv64 s64 v51 v69
  store_step with Store.apply_rep s65 v34 v70 _ _ hinv65 h64 h_v34 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s66, hinv66, h_v71⟩ growing hG carrying h_v13 h_v14 h_v23 dropping h_v34 h_v70 hinv65 s65 v34 v70
  store_step with Store.apply_rep s66 v23 v71 _ _ hinv66 h64 h_v23 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s67, hinv67, h_v72⟩ growing hG carrying h_v13 h_v14 dropping h_v23 h_v71 hinv66 s66 v23 v71
  store_step with Store.apply_rep s67 v14 v72 _ _ hinv67 h64 h_v14 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s68, hinv68, h_v73⟩ growing hG carrying h_v13 dropping h_v14 h_v72 hinv67 s67 v14 v72
  store_step with Store.apply_rep s68 v13 v73 _ _ hinv68 h64 h_v13 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s69, hinv69, h_v74⟩ growing hG carrying dropping h_v13 h_v73 hinv68 s68 v13 v73
  case_done hinv69 hG with h_v74 in EoCases.__str_reduction_pred.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 6450000 in
theorem case_1_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_1
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_1
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_1
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_and.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3e_3d.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with Store.apply_rep s4 v12 v5 _ _ hinv4 h64 h_v12 h_v5 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v12 hinv4 s4 v12
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 dropping hinv5 s5
  store_step with Store.apply_rep s6 v13 v14 _ _ hinv6 h64 h_v13 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v13 h_v14 hinv6 s6 v13 v14
  store_step with Store.apply_rep s7 v11 v15 _ _ hinv7 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 h_v15 hinv7 s7 v11 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_and.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 dropping he_v17 hinv8 e_v17 s8
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3e.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v17 dropping he_v18 hinv9 e_v18 s9
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v17 h_v18 dropping he_v19 hinv10 e_v19 s10
  store_step with Store.apply_rep s11 v19 v8 _ _ hinv11 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v17 h_v18 dropping h_v19 hinv11 s11 v19
  store_step with Store.apply_rep s12 v18 v20 _ _ hinv12 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v17 dropping h_v18 h_v20 hinv12 s12 v18 v20
  store_step with Store.apply_rep s13 v21 v5 _ _ hinv13 h64 h_v21 h_v5 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v17 dropping h_v21 hinv13 s13 v21
  store_step with Store.apply_rep s14 v17 v22 _ _ hinv14 h64 h_v17 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 dropping h_v17 h_v22 hinv14 s14 v17 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_and.construct s15 e_v24 (by rw [he_v24]; exact empty_args) hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 dropping he_v24 hinv15 e_v24 s15
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3e.construct s16 e_v25 (by rw [he_v25]; exact empty_args) hinv16 h64 as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 h_v24 dropping he_v25 hinv16 e_v25 s16
  store_step with Store.apply_rep s17 v25 v2 _ _ hinv17 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 h_v24 dropping h_v25 hinv17 s17 v25
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 h_v24 h_v26 dropping hinv18 s18
  store_step with Store.apply_rep s19 v26 v27 _ _ hinv19 h64 h_v26 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 h_v24 dropping h_v26 h_v27 hinv19 s19 v26 v27
  store_step with Store.apply_rep s20 v24 v28 _ _ hinv20 h64 h_v24 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 dropping h_v24 h_v28 hinv20 s20 v24 v28
  store_step with Store.literal_boolean_spec s21 true hinv21 h64 as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 h_v29 dropping hinv21 s21
  store_step with Store.apply_rep s22 v29 v30 _ _ hinv22 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 dropping h_v29 h_v30 hinv22 s22 v29 v30
  store_step with Store.apply_rep s23 v23 v31 _ _ hinv23 h64 h_v23 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 dropping h_v23 h_v31 hinv23 s23 v23 v31
  store_step with Store.apply_rep s24 v16 v32 _ _ hinv24 h64 h_v16 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v16 h_v32 hinv24 s24 v16 v32
  store_step with Store.apply_rep s25 v10 v33 _ _ hinv25 h64 h_v10 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v33 hinv25 s25 v10 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_and.construct s26 e_v35 (by rw [he_v35]; exact empty_args) hinv26 h64 as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 dropping he_v35 hinv26 e_v35 s26
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3d.construct s27 e_v36 (by rw [he_v36]; exact empty_args) hinv27 h64 as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 dropping he_v36 hinv27 e_v36 s27
  store_step with Store.apply_rep s28 v36 v8 _ _ hinv28 h64 h_v36 h_v8 (by ns_tac) (by ns_tac) as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 dropping h_v36 hinv28 s28 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s29 e_v38 (by rw [he_v38]; exact empty_args) hinv29 h64 as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 dropping he_v38 hinv29 e_v38 s29
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__40purify.construct s30 e_v39 (by rw [he_v39]; exact empty_args) hinv30 h64 as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 dropping he_v39 hinv30 e_v39 s30
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s31 e_v40 (by rw [he_v40]; exact empty_args) hinv31 h64 as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 h_v39 dropping he_v40 hinv31 e_v40 s31
  store_step with Store.apply_rep s32 v40 v8 _ _ hinv32 h64 h_v40 h_v8 (by ns_tac) (by ns_tac) as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 h_v39 dropping h_v40 hinv32 s32 v40
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s33 0#u32 (0) (by scalar_tac) hinv33 h64 as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 h_v39 h_v41 dropping hinv33 s33
  store_step with Store.apply_rep s34 v41 v42 _ _ hinv34 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 h_v39 dropping h_v41 h_v42 hinv34 s34 v41 v42
  store_step with Store.apply_rep s35 v43 v5 _ _ hinv35 h64 h_v43 h_v5 (by ns_tac) (by ns_tac) as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 h_v39 dropping h_v43 hinv35 s35 v43
  store_step with Store.apply_rep s36 v39 v44 _ _ hinv36 h64 h_v39 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v38 dropping h_v39 h_v44 hinv36 s36 v39 v44
  store_step with Store.apply_rep s37 v38 v45 _ _ hinv37 h64 h_v38 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 dropping h_v38 h_v45 hinv37 s37 v38 v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s38 e_v47 (by rw [he_v47]; exact empty_args) hinv38 h64 as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 dropping he_v47 hinv38 e_v47 s38
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__40purify.construct s39 e_v48 (by rw [he_v48]; exact empty_args) hinv39 h64 as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v47 dropping he_v48 hinv39 e_v48 s39
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s40 e_v49 (by rw [he_v49]; exact empty_args) hinv40 h64 as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v47 h_v48 dropping he_v49 hinv40 e_v49 s40
  store_step with Store.apply_rep s41 v49 v8 _ _ hinv41 h64 h_v49 h_v8 (by ns_tac) (by ns_tac) as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v47 h_v48 dropping h_v49 hinv41 s41 v49
  store_step with Store.apply_rep s42 v50 v5 _ _ hinv42 h64 h_v50 h_v5 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v47 h_v48 dropping h_v50 hinv42 s42 v50
  store_step with Store.apply_rep s43 v51 v2 _ _ hinv43 h64 h_v51 h_v2 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v47 h_v48 dropping h_v51 hinv43 s43 v51
  store_step with Store.apply_rep s44 v48 v52 _ _ hinv44 h64 h_v48 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v47 dropping h_v48 h_v52 hinv44 s44 v48 v52
  store_step with Store.apply_rep s45 v47 v53 _ _ hinv45 h64 h_v47 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 dropping h_v47 h_v53 hinv45 s45 v47 v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s46 e_v55 (by rw [he_v55]; exact empty_args) hinv46 h64 as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 dropping he_v55 hinv46 e_v55 s46
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__40purify.construct s47 e_v56 (by rw [he_v56]; exact empty_args) hinv47 h64 as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 dropping he_v56 hinv47 e_v56 s47
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s48 e_v57 (by rw [he_v57]; exact empty_args) hinv48 h64 as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 dropping he_v57 hinv48 e_v57 s48
  store_step with Store.apply_rep s49 v57 v8 _ _ hinv49 h64 h_v57 h_v8 (by ns_tac) (by ns_tac) as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 dropping h_v57 hinv49 s49 v57
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__2b.construct s50 e_v59 (by rw [he_v59]; exact empty_args) hinv50 h64 as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 dropping he_v59 hinv50 e_v59 s50
  store_step with Store.apply_rep s51 v59 v5 _ _ hinv51 h64 h_v59 h_v5 (by ns_tac) (by ns_tac) as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 dropping h_v59 hinv51 s51 v59
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__2b.construct s52 e_v61 (by rw [he_v61]; exact empty_args) hinv52 h64 as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 h_v60 dropping he_v61 hinv52 e_v61 s52
  store_step with Store.apply_rep s53 v61 v2 _ _ hinv53 h64 h_v61 h_v2 (by ns_tac) (by ns_tac) as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 h_v60 dropping h_v61 hinv53 s53 v61
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s54 0#u32 (0) (by scalar_tac) hinv54 h64 as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 h_v60 h_v62 dropping hinv54 s54
  store_step with Store.apply_rep s55 v62 v63 _ _ hinv55 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 h_v60 dropping h_v62 h_v63 hinv55 s55 v62 v63
  store_step with Store.apply_rep s56 v60 v64 _ _ hinv56 h64 h_v60 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v58 dropping h_v60 h_v64 hinv56 s56 v60 v64
  store_step with Store.apply_rep s57 v58 v65 _ _ hinv57 h64 h_v58 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 dropping h_v58 h_v65 hinv57 s57 v58 v65
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo__2d.construct s58 e_v67 (by rw [he_v67]; exact empty_args) hinv58 h64 as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 dropping he_v67 hinv58 e_v67 s58
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo_str_2elen.construct s59 e_v68 (by rw [he_v68]; exact empty_args) hinv59 h64 as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v67 dropping he_v68 hinv59 e_v68 s59
  store_step with Store.apply_rep s60 v68 v8 _ _ hinv60 h64 h_v68 h_v8 (by ns_tac) (by ns_tac) as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v67 dropping h_v68 hinv60 s60 v68
  store_step with Store.apply_rep s61 v67 v69 _ _ hinv61 h64 h_v67 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 dropping h_v67 h_v69 hinv61 s61 v67 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo__2b.construct s62 e_v71 (by rw [he_v71]; exact empty_args) hinv62 h64 as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 dropping he_v71 hinv62 e_v71 s62
  store_step with Store.apply_rep s63 v71 v5 _ _ hinv63 h64 h_v71 h_v5 (by ns_tac) (by ns_tac) as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 dropping h_v71 hinv63 s63 v71
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo__2b.construct s64 e_v73 (by rw [he_v73]; exact empty_args) hinv64 h64 as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 h_v72 dropping he_v73 hinv64 e_v73 s64
  store_step with Store.apply_rep s65 v73 v2 _ _ hinv65 h64 h_v73 h_v2 (by ns_tac) (by ns_tac) as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 h_v72 dropping h_v73 hinv65 s65 v73
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s66 0#u32 (0) (by scalar_tac) hinv66 h64 as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 h_v72 h_v74 dropping hinv66 s66
  store_step with Store.apply_rep s67 v74 v75 _ _ hinv67 h64 h_v74 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 h_v72 dropping h_v74 h_v75 hinv67 s67 v74 v75
  store_step with Store.apply_rep s68 v72 v76 _ _ hinv68 h64 h_v72 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 h_v70 dropping h_v72 h_v76 hinv68 s68 v72 v76
  store_step with Store.apply_rep s69 v70 v77 _ _ hinv69 h64 h_v70 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 h_v66 dropping h_v70 h_v77 hinv69 s69 v70 v77
  store_step with Store.apply_rep s70 v66 v78 _ _ hinv70 h64 h_v66 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 h_v56 dropping h_v66 h_v78 hinv70 s70 v66 v78
  store_step with Store.apply_rep s71 v56 v79 _ _ hinv71 h64 h_v56 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v55 dropping h_v56 h_v79 hinv71 s71 v56 v79
  store_step with Store.apply_rep s72 v55 v80 _ _ hinv72 h64 h_v55 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 dropping h_v55 h_v80 hinv72 s72 v55 v80
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s73 e_v82 (by rw [he_v82]; exact empty_args) hinv73 h64 as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 dropping he_v82 hinv73 e_v82 s73
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo__40purify.construct s74 e_v83 (by rw [he_v83]; exact empty_args) hinv74 h64 as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 dropping he_v83 hinv74 e_v83 s74
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s75 e_v84 (by rw [he_v84]; exact empty_args) hinv75 h64 as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 h_v83 dropping he_v84 hinv75 e_v84 s75
  store_step with Store.apply_rep s76 v84 v8 _ _ hinv76 h64 h_v84 h_v8 (by ns_tac) (by ns_tac) as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 h_v83 dropping h_v84 hinv76 s76 v84
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s77 0#u32 (0) (by scalar_tac) hinv77 h64 as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 h_v83 h_v85 dropping hinv77 s77
  store_step with Store.apply_rep s78 v85 v86 _ _ hinv78 h64 h_v85 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 h_v83 dropping h_v85 h_v86 hinv78 s78 v85 v86
  store_step with Store.apply_rep s79 v87 v5 _ _ hinv79 h64 h_v87 h_v5 (by ns_tac) (by ns_tac) as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 h_v83 dropping h_v87 hinv79 s79 v87
  store_step with Store.apply_rep s80 v83 v88 _ _ hinv80 h64 h_v83 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 dropping h_v83 h_v88 hinv80 s80 v83 v88
  store_step with ih.eo__24eo_5ftypeof s81 v89 _ hinv81 h64 (hG.rem hrem) h_v89 as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 h_v82 dropping h_v89 hinv81 s81 v89
  store_step with ih.eo__24eo_5fnil s82 v82 v90 _ _ hinv82 h64 (hG.rem hrem) h_v82 h_v90 as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 h_v81 dropping h_v82 h_v90 hinv82 s82 v82 v90
  store_step with Store.apply_mk_rep s83 v81 v91 _ _ hinv83 h64 h_v81 h_v91 as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 h_v54 dropping h_v81 h_v91 hinv83 s83 v81 v91
  store_step with Store.apply_mk_rep s84 v54 v92 _ _ hinv84 h64 h_v54 h_v92 as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 h_v46 dropping h_v54 h_v92 hinv84 s84 v54 v92
  store_step with Store.apply_mk_rep s85 v46 v93 _ _ hinv85 h64 h_v46 h_v93 as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 h_v37 dropping h_v46 h_v93 hinv85 s85 v46 v93
  store_step with Store.apply_mk_rep s86 v37 v94 _ _ hinv86 h64 h_v37 h_v94 as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v35 dropping h_v37 h_v94 hinv86 s86 v37 v94
  store_step with Store.apply_mk_rep s87 v35 v95 _ _ hinv87 h64 h_v35 h_v95 as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 dropping h_v35 h_v95 hinv87 s87 v35 v95
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_and.construct s88 e_v97 (by rw [he_v97]; exact empty_args) hinv88 h64 as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 dropping he_v97 hinv88 e_v97 s88
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo__3d.construct s89 e_v98 (by rw [he_v98]; exact empty_args) hinv89 h64 as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 dropping he_v98 hinv89 e_v98 s89
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_str_2elen.construct s90 e_v99 (by rw [he_v99]; exact empty_args) hinv90 h64 as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 dropping he_v99 hinv90 e_v99 s90
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo__40purify.construct s91 e_v100 (by rw [he_v100]; exact empty_args) hinv91 h64 as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 dropping he_v100 hinv91 e_v100 s91
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s92 e_v101 (by rw [he_v101]; exact empty_args) hinv92 h64 as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 h_v100 dropping he_v101 hinv92 e_v101 s92
  store_step with Store.apply_rep s93 v101 v8 _ _ hinv93 h64 h_v101 h_v8 (by ns_tac) (by ns_tac) as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 h_v100 dropping h_v101 hinv93 s93 v101
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s94 0#u32 (0) (by scalar_tac) hinv94 h64 as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 h_v100 h_v102 dropping hinv94 s94
  store_step with Store.apply_rep s95 v102 v103 _ _ hinv95 h64 h_v102 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 h_v100 dropping h_v102 h_v103 hinv95 s95 v102 v103
  store_step with Store.apply_rep s96 v104 v5 _ _ hinv96 h64 h_v104 h_v5 (by ns_tac) (by ns_tac) as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 h_v100 dropping h_v104 hinv96 s96 v104
  store_step with Store.apply_rep s97 v100 v105 _ _ hinv97 h64 h_v100 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 h_v99 dropping h_v100 h_v105 hinv97 s97 v100 v105
  store_step with Store.apply_rep s98 v99 v106 _ _ hinv98 h64 h_v99 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 h_v98 dropping h_v106 h_v99 hinv98 s98 v106 v99
  store_step with Store.apply_rep s99 v98 v107 _ _ hinv99 h64 h_v98 h_v107 (by ns_tac) (by ns_tac) as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 dropping h_v107 h_v98 hinv99 s99 v107 v98
  store_step with Store.apply_rep s100 v108 v5 _ _ hinv100 h64 h_v108 h_v5 (by ns_tac) (by ns_tac) as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v97 dropping h_v108 hinv100 s100 v108
  store_step with Store.apply_rep s101 v97 v109 _ _ hinv101 h64 h_v97 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 dropping h_v109 h_v97 hinv101 s101 v109 v97
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo_and.construct s102 e_v111 (by rw [he_v111]; exact empty_args) hinv102 h64 as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 dropping he_v111 hinv102 e_v111 s102
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo_or.construct s103 e_v112 (by rw [he_v112]; exact empty_args) hinv103 h64 as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 dropping he_v112 hinv103 e_v112 s103
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo__3d.construct s104 e_v113 (by rw [he_v113]; exact empty_args) hinv104 h64 as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 dropping he_v113 hinv104 e_v113 s104
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_str_2elen.construct s105 e_v114 (by rw [he_v114]; exact empty_args) hinv105 h64 as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 dropping he_v114 hinv105 e_v114 s105
  step as ⟨e_v115, he_v115⟩
  store_step with CtorSpec.eo__40purify.construct s106 e_v115 (by rw [he_v115]; exact empty_args) hinv106 h64 as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 dropping he_v115 hinv106 e_v115 s106
  step as ⟨e_v116, he_v116⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s107 e_v116 (by rw [he_v116]; exact empty_args) hinv107 h64 as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 dropping he_v116 hinv107 e_v116 s107
  store_step with Store.apply_rep s108 v116 v8 _ _ hinv108 h64 h_v116 h_v8 (by ns_tac) (by ns_tac) as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 dropping h_v116 hinv108 s108 v116
  step as ⟨e_v118, he_v118⟩
  store_step with CtorSpec.eo__2b.construct s109 e_v118 (by rw [he_v118]; exact empty_args) hinv109 h64 as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 dropping he_v118 hinv109 e_v118 s109
  store_step with Store.apply_rep s110 v118 v5 _ _ hinv110 h64 h_v118 h_v5 (by ns_tac) (by ns_tac) as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 dropping h_v118 hinv110 s110 v118
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__2b.construct s111 e_v120 (by rw [he_v120]; exact empty_args) hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 h_v119 dropping he_v120 hinv111 e_v120 s111
  store_step with Store.apply_rep s112 v120 v2 _ _ hinv112 h64 h_v120 h_v2 (by ns_tac) (by ns_tac) as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 h_v119 dropping h_v120 hinv112 s112 v120
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s113 0#u32 (0) (by scalar_tac) hinv113 h64 as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 h_v119 h_v121 dropping hinv113 s113
  store_step with Store.apply_rep s114 v121 v122 _ _ hinv114 h64 h_v121 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 h_v119 dropping h_v121 h_v122 hinv114 s114 v121 v122
  store_step with Store.apply_rep s115 v119 v123 _ _ hinv115 h64 h_v119 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v117 dropping h_v119 h_v123 hinv115 s115 v119 v123
  store_step with Store.apply_rep s116 v117 v124 _ _ hinv116 h64 h_v117 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 dropping h_v117 h_v124 hinv116 s116 v117 v124
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo__2d.construct s117 e_v126 (by rw [he_v126]; exact empty_args) hinv117 h64 as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 dropping he_v126 hinv117 e_v126 s117
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo_str_2elen.construct s118 e_v127 (by rw [he_v127]; exact empty_args) hinv118 h64 as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v126 dropping he_v127 hinv118 e_v127 s118
  store_step with Store.apply_rep s119 v127 v8 _ _ hinv119 h64 h_v127 h_v8 (by ns_tac) (by ns_tac) as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v126 dropping h_v127 hinv119 s119 v127
  store_step with Store.apply_rep s120 v126 v128 _ _ hinv120 h64 h_v126 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 dropping h_v126 h_v128 hinv120 s120 v126 v128
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo__2b.construct s121 e_v130 (by rw [he_v130]; exact empty_args) hinv121 h64 as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 dropping he_v130 hinv121 e_v130 s121
  store_step with Store.apply_rep s122 v130 v5 _ _ hinv122 h64 h_v130 h_v5 (by ns_tac) (by ns_tac) as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 dropping h_v130 hinv122 s122 v130
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo__2b.construct s123 e_v132 (by rw [he_v132]; exact empty_args) hinv123 h64 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 h_v131 dropping he_v132 hinv123 e_v132 s123
  store_step with Store.apply_rep s124 v132 v2 _ _ hinv124 h64 h_v132 h_v2 (by ns_tac) (by ns_tac) as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 h_v131 dropping h_v132 hinv124 s124 v132
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s125 0#u32 (0) (by scalar_tac) hinv125 h64 as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 h_v131 h_v133 dropping hinv125 s125
  store_step with Store.apply_rep s126 v133 v134 _ _ hinv126 h64 h_v133 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 h_v131 dropping h_v133 h_v134 hinv126 s126 v133 v134
  store_step with Store.apply_rep s127 v131 v135 _ _ hinv127 h64 h_v131 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 h_v129 dropping h_v131 h_v135 hinv127 s127 v131 v135
  store_step with Store.apply_rep s128 v129 v136 _ _ hinv128 h64 h_v129 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v125 dropping h_v129 h_v136 hinv128 s128 v129 v136
  store_step with Store.apply_rep s129 v125 v137 _ _ hinv129 h64 h_v125 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 dropping h_v125 h_v137 hinv129 s129 v125 v137
  store_step with Store.apply_rep s130 v115 v138 _ _ hinv130 h64 h_v115 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 h_v114 dropping h_v115 h_v138 hinv130 s130 v115 v138
  store_step with Store.apply_rep s131 v114 v139 _ _ hinv131 h64 h_v114 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v113 dropping h_v114 h_v139 hinv131 s131 v114 v139
  store_step with Store.apply_rep s132 v113 v140 _ _ hinv132 h64 h_v113 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 dropping h_v113 h_v140 hinv132 s132 v113 v140
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo__2d.construct s133 e_v142 (by rw [he_v142]; exact empty_args) hinv133 h64 as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 dropping he_v142 hinv133 e_v142 s133
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_str_2elen.construct s134 e_v143 (by rw [he_v143]; exact empty_args) hinv134 h64 as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v142 dropping he_v143 hinv134 e_v143 s134
  store_step with Store.apply_rep s135 v143 v8 _ _ hinv135 h64 h_v143 h_v8 (by ns_tac) (by ns_tac) as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v142 dropping h_v143 hinv135 s135 v143
  store_step with Store.apply_rep s136 v142 v144 _ _ hinv136 h64 h_v142 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 dropping h_v142 h_v144 hinv136 s136 v142 v144
  step as ⟨e_v146, he_v146⟩
  store_step with CtorSpec.eo__2b.construct s137 e_v146 (by rw [he_v146]; exact empty_args) hinv137 h64 as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 dropping he_v146 hinv137 e_v146 s137
  store_step with Store.apply_rep s138 v146 v5 _ _ hinv138 h64 h_v146 h_v5 (by ns_tac) (by ns_tac) as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 dropping h_v146 hinv138 s138 v146
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo__2b.construct s139 e_v148 (by rw [he_v148]; exact empty_args) hinv139 h64 as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 h_v147 dropping he_v148 hinv139 e_v148 s139
  store_step with Store.apply_rep s140 v148 v2 _ _ hinv140 h64 h_v148 h_v2 (by ns_tac) (by ns_tac) as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 h_v147 dropping h_v148 hinv140 s140 v148
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s141 0#u32 (0) (by scalar_tac) hinv141 h64 as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 h_v147 h_v149 dropping hinv141 s141
  store_step with Store.apply_rep s142 v149 v150 _ _ hinv142 h64 h_v149 h_v150 (by ns_tac) (by ns_tac) as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 h_v147 dropping h_v149 h_v150 hinv142 s142 v149 v150
  store_step with Store.apply_rep s143 v147 v151 _ _ hinv143 h64 h_v147 h_v151 (by ns_tac) (by ns_tac) as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 h_v145 dropping h_v147 h_v151 hinv143 s143 v147 v151
  store_step with Store.apply_rep s144 v145 v152 _ _ hinv144 h64 h_v145 h_v152 (by ns_tac) (by ns_tac) as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 h_v141 dropping h_v145 h_v152 hinv144 s144 v145 v152
  store_step with Store.apply_rep s145 v141 v153 _ _ hinv145 h64 h_v141 h_v153 (by ns_tac) (by ns_tac) as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v112 dropping h_v141 h_v153 hinv145 s145 v141 v153
  store_step with Store.apply_rep s146 v112 v154 _ _ hinv146 h64 h_v112 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 dropping h_v112 h_v154 hinv146 s146 v112 v154
  step as ⟨e_v156, he_v156⟩
  store_step with CtorSpec.eo_or.construct s147 e_v156 (by rw [he_v156]; exact empty_args) hinv147 h64 as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 dropping he_v156 hinv147 e_v156 s147
  step as ⟨e_v157, he_v157⟩
  store_step with CtorSpec.eo__3d.construct s148 e_v157 (by rw [he_v157]; exact empty_args) hinv148 h64 as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 dropping he_v157 hinv148 e_v157 s148
  step as ⟨e_v158, he_v158⟩
  store_step with CtorSpec.eo_str_2elen.construct s149 e_v158 (by rw [he_v158]; exact empty_args) hinv149 h64 as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 dropping he_v158 hinv149 e_v158 s149
  step as ⟨e_v159, he_v159⟩
  store_step with CtorSpec.eo__40purify.construct s150 e_v159 (by rw [he_v159]; exact empty_args) hinv150 h64 as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 dropping he_v159 hinv150 e_v159 s150
  step as ⟨e_v160, he_v160⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s151 e_v160 (by rw [he_v160]; exact empty_args) hinv151 h64 as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 dropping he_v160 hinv151 e_v160 s151
  store_step with Store.apply_rep s152 v160 v8 _ _ hinv152 h64 h_v160 h_v8 (by ns_tac) (by ns_tac) as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 dropping h_v160 hinv152 s152 v160
  step as ⟨e_v162, he_v162⟩
  store_step with CtorSpec.eo__2b.construct s153 e_v162 (by rw [he_v162]; exact empty_args) hinv153 h64 as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 dropping he_v162 hinv153 e_v162 s153
  store_step with Store.apply_rep s154 v162 v5 _ _ hinv154 h64 h_v162 h_v5 (by ns_tac) (by ns_tac) as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 dropping h_v162 hinv154 s154 v162
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo__2b.construct s155 e_v164 (by rw [he_v164]; exact empty_args) hinv155 h64 as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 h_v163 dropping he_v164 hinv155 e_v164 s155
  store_step with Store.apply_rep s156 v164 v2 _ _ hinv156 h64 h_v164 h_v2 (by ns_tac) (by ns_tac) as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 h_v163 dropping h_v164 hinv156 s156 v164
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s157 0#u32 (0) (by scalar_tac) hinv157 h64 as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 h_v163 h_v165 dropping hinv157 s157
  store_step with Store.apply_rep s158 v165 v166 _ _ hinv158 h64 h_v165 h_v166 (by ns_tac) (by ns_tac) as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 h_v163 dropping h_v165 h_v166 hinv158 s158 v165 v166
  store_step with Store.apply_rep s159 v163 v167 _ _ hinv159 h64 h_v163 h_v167 (by ns_tac) (by ns_tac) as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v161 dropping h_v163 h_v167 hinv159 s159 v163 v167
  store_step with Store.apply_rep s160 v161 v168 _ _ hinv160 h64 h_v161 h_v168 (by ns_tac) (by ns_tac) as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 dropping h_v161 h_v168 hinv160 s160 v161 v168
  step as ⟨e_v170, he_v170⟩
  store_step with CtorSpec.eo__2d.construct s161 e_v170 (by rw [he_v170]; exact empty_args) hinv161 h64 as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 dropping he_v170 hinv161 e_v170 s161
  step as ⟨e_v171, he_v171⟩
  store_step with CtorSpec.eo_str_2elen.construct s162 e_v171 (by rw [he_v171]; exact empty_args) hinv162 h64 as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v170 dropping he_v171 hinv162 e_v171 s162
  store_step with Store.apply_rep s163 v171 v8 _ _ hinv163 h64 h_v171 h_v8 (by ns_tac) (by ns_tac) as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v170 dropping h_v171 hinv163 s163 v171
  store_step with Store.apply_rep s164 v170 v172 _ _ hinv164 h64 h_v170 h_v172 (by ns_tac) (by ns_tac) as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 dropping h_v170 h_v172 hinv164 s164 v170 v172
  step as ⟨e_v174, he_v174⟩
  store_step with CtorSpec.eo__2b.construct s165 e_v174 (by rw [he_v174]; exact empty_args) hinv165 h64 as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 dropping he_v174 hinv165 e_v174 s165
  store_step with Store.apply_rep s166 v174 v5 _ _ hinv166 h64 h_v174 h_v5 (by ns_tac) (by ns_tac) as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 dropping h_v174 hinv166 s166 v174
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo__2b.construct s167 e_v176 (by rw [he_v176]; exact empty_args) hinv167 h64 as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 h_v175 dropping he_v176 hinv167 e_v176 s167
  store_step with Store.apply_rep s168 v176 v2 _ _ hinv168 h64 h_v176 h_v2 (by ns_tac) (by ns_tac) as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 h_v175 dropping h_v176 hinv168 s168 v176
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s169 0#u32 (0) (by scalar_tac) hinv169 h64 as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 h_v175 h_v177 dropping hinv169 s169
  store_step with Store.apply_rep s170 v177 v178 _ _ hinv170 h64 h_v177 h_v178 (by ns_tac) (by ns_tac) as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 h_v175 dropping h_v177 h_v178 hinv170 s170 v177 v178
  store_step with Store.apply_rep s171 v175 v179 _ _ hinv171 h64 h_v175 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 h_v173 dropping h_v175 h_v179 hinv171 s171 v175 v179
  store_step with Store.apply_rep s172 v173 v180 _ _ hinv172 h64 h_v173 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 h_v169 dropping h_v173 h_v180 hinv172 s172 v173 v180
  store_step with Store.apply_rep s173 v169 v181 _ _ hinv173 h64 h_v169 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 h_v159 dropping h_v169 h_v181 hinv173 s173 v169 v181
  store_step with Store.apply_rep s174 v159 v182 _ _ hinv174 h64 h_v159 h_v182 (by ns_tac) (by ns_tac) as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 h_v158 dropping h_v159 h_v182 hinv174 s174 v159 v182
  store_step with Store.apply_rep s175 v158 v183 _ _ hinv175 h64 h_v158 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v157 dropping h_v158 h_v183 hinv175 s175 v158 v183
  store_step with Store.apply_rep s176 v157 v184 _ _ hinv176 h64 h_v157 h_v184 (by ns_tac) (by ns_tac) as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 dropping h_v157 h_v184 hinv176 s176 v157 v184
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s177 0#u32 (0) (by scalar_tac) hinv177 h64 as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 h_v185 dropping hinv177 s177
  store_step with Store.apply_rep s178 v185 v186 _ _ hinv178 h64 h_v185 h_v186 (by ns_tac) (by ns_tac) as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v156 dropping h_v185 h_v186 hinv178 s178 v185 v186
  store_step with Store.apply_rep s179 v156 v187 _ _ hinv179 h64 h_v156 h_v187 (by ns_tac) (by ns_tac) as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 dropping h_v156 h_v187 hinv179 s179 v156 v187
  store_step with Store.literal_boolean_spec s180 false hinv180 h64 as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 h_v188 dropping hinv180 s180
  store_step with Store.apply_rep s181 v188 v189 _ _ hinv181 h64 h_v188 h_v189 (by ns_tac) (by ns_tac) as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 h_v155 dropping h_v188 h_v189 hinv181 s181 v188 v189
  store_step with Store.apply_rep s182 v155 v190 _ _ hinv182 h64 h_v155 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v111 dropping h_v155 h_v190 hinv182 s182 v155 v190
  store_step with Store.apply_rep s183 v111 v191 _ _ hinv183 h64 h_v111 h_v191 (by ns_tac) (by ns_tac) as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 dropping h_v111 h_v191 hinv183 s183 v111 v191
  step as ⟨e_v193, he_v193⟩
  store_step with CtorSpec.eo_and.construct s184 e_v193 (by rw [he_v193]; exact empty_args) hinv184 h64 as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 dropping he_v193 hinv184 e_v193 s184
  step as ⟨e_v194, he_v194⟩
  store_step with CtorSpec.eo__3c_3d.construct s185 e_v194 (by rw [he_v194]; exact empty_args) hinv185 h64 as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 dropping he_v194 hinv185 e_v194 s185
  step as ⟨e_v195, he_v195⟩
  store_step with CtorSpec.eo_str_2elen.construct s186 e_v195 (by rw [he_v195]; exact empty_args) hinv186 h64 as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 dropping he_v195 hinv186 e_v195 s186
  step as ⟨e_v196, he_v196⟩
  store_step with CtorSpec.eo__40purify.construct s187 e_v196 (by rw [he_v196]; exact empty_args) hinv187 h64 as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 h_v195 dropping he_v196 hinv187 e_v196 s187
  step as ⟨e_v197, he_v197⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s188 e_v197 (by rw [he_v197]; exact empty_args) hinv188 h64 as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 h_v195 h_v196 dropping he_v197 hinv188 e_v197 s188
  store_step with Store.apply_rep s189 v197 v8 _ _ hinv189 h64 h_v197 h_v8 (by ns_tac) (by ns_tac) as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 h_v195 h_v196 dropping h_v197 hinv189 s189 v197
  store_step with Store.apply_rep s190 v198 v5 _ _ hinv190 h64 h_v198 h_v5 (by ns_tac) (by ns_tac) as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 h_v195 h_v196 dropping h_v198 hinv190 s190 v198
  store_step with Store.apply_rep s191 v199 v2 _ _ hinv191 h64 h_v199 h_v2 (by ns_tac) (by ns_tac) as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 h_v195 h_v196 dropping h_v199 hinv191 s191 v199
  store_step with Store.apply_rep s192 v196 v200 _ _ hinv192 h64 h_v196 h_v200 (by ns_tac) (by ns_tac) as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 h_v195 dropping h_v196 h_v200 hinv192 s192 v196 v200
  store_step with Store.apply_rep s193 v195 v201 _ _ hinv193 h64 h_v195 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 h_v194 dropping h_v195 h_v201 hinv193 s193 v195 v201
  store_step with Store.apply_rep s194 v194 v202 _ _ hinv194 h64 h_v194 h_v202 (by ns_tac) (by ns_tac) as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 dropping h_v194 h_v202 hinv194 s194 v194 v202
  store_step with Store.apply_rep s195 v203 v2 _ _ hinv195 h64 h_v203 h_v2 (by ns_tac) (by ns_tac) as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v193 dropping h_v203 hinv195 s195 v203
  store_step with Store.apply_rep s196 v193 v204 _ _ hinv196 h64 h_v193 h_v204 (by ns_tac) (by ns_tac) as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 dropping h_v193 h_v204 hinv196 s196 v193 v204
  store_step with Store.literal_boolean_spec s197 true hinv197 h64 as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 h_v205 dropping hinv197 s197
  store_step with Store.apply_rep s198 v205 v206 _ _ hinv198 h64 h_v205 h_v206 (by ns_tac) (by ns_tac) as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 h_v192 dropping h_v205 h_v206 hinv198 s198 v205 v206
  store_step with Store.apply_rep s199 v192 v207 _ _ hinv199 h64 h_v192 h_v207 (by ns_tac) (by ns_tac) as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 h_v110 dropping h_v192 h_v207 hinv199 s199 v192 v207
  store_step with Store.apply_rep s200 v110 v208 _ _ hinv200 h64 h_v110 h_v208 (by ns_tac) (by ns_tac) as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 h_v96 dropping h_v110 h_v208 hinv200 s200 v110 v208
  store_step with Store.apply_mk_rep s201 v96 v209 _ _ hinv201 h64 h_v96 h_v209 as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v34 dropping h_v209 h_v96 hinv201 s201 v209 v96
  store_step with Store.apply_mk_rep s202 v34 v210 _ _ hinv202 h64 h_v34 h_v210 as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v210 h_v34 hinv202 s202 v210 v34
  step as ⟨e_v212, he_v212⟩
  store_step with CtorSpec.eo__3d.construct s203 e_v212 (by rw [he_v212]; exact empty_args) hinv203 h64 as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v211 dropping he_v212 hinv203 e_v212 s203
  step as ⟨e_v213, he_v213⟩
  store_step with CtorSpec.eo__40purify.construct s204 e_v213 (by rw [he_v213]; exact empty_args) hinv204 h64 as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v211 h_v212 dropping he_v213 hinv204 e_v213 s204
  step as ⟨e_v214, he_v214⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s205 e_v214 (by rw [he_v214]; exact empty_args) hinv205 h64 as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v211 h_v212 h_v213 dropping he_v214 hinv205 e_v214 s205
  store_step with Store.apply_rep s206 v214 v8 _ _ hinv206 h64 h_v214 h_v8 (by ns_tac) (by ns_tac) as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v211 h_v212 h_v213 dropping h_v214 hinv206 s206 v214
  store_step with Store.apply_rep s207 v215 v5 _ _ hinv207 h64 h_v215 h_v5 (by ns_tac) (by ns_tac) as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v2 h_v8 h_v211 h_v212 h_v213 dropping h_v215 h_v5 hinv207 s207 v215 v5
  store_step with Store.apply_rep s208 v216 v2 _ _ hinv208 h64 h_v216 h_v2 (by ns_tac) (by ns_tac) as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v8 h_v211 h_v212 h_v213 dropping h_v2 h_v216 hinv208 s208 v2 v216
  store_step with Store.apply_rep s209 v213 v217 _ _ hinv209 h64 h_v213 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v8 h_v211 h_v212 dropping h_v213 h_v217 hinv209 s209 v213 v217
  store_step with Store.apply_rep s210 v212 v218 _ _ hinv210 h64 h_v212 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v8 h_v211 dropping h_v212 h_v218 hinv210 s210 v212 v218
  store_step with ih.eo__24eo_5ftypeof s211 v8 _ hinv211 h64 (hG.rem hrem) h_v8 as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v211 h_v219 dropping h_v8 hinv211 s211 v8
  store_step with ih.eo__24seq_5fempty s212 v220 _ hinv212 h64 (hG.rem hrem) h_v220 as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v211 h_v219 dropping h_v220 hinv212 s212 v220
  store_step with Store.apply_mk_rep s213 v219 v221 _ _ hinv213 h64 h_v219 h_v221 as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v211 dropping h_v219 h_v221 hinv213 s213 v219 v221
  store_step with Store.apply_mk_rep s214 v211 v222 _ _ hinv214 h64 h_v211 h_v222 as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying dropping h_v211 h_v222 hinv214 s214 v211 v222
  case_done hinv215 hG with h_v223 in EoCases.__str_reduction_pred.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

set_option maxHeartbeats 12120000 in
theorem case_2_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_2
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_2
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_not.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v13 (by rw [he_v13]; exact empty_args) hinv4 h64 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 dropping he_v13 hinv4 e_v13 s4
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 dropping he_v14 hinv5 e_v14 s5
  store_step with Store.apply_rep s6 v14 v8 _ _ hinv6 h64 h_v14 h_v8 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 dropping h_v14 hinv6 s6 v14
  store_step with Store.apply_rep s7 v15 v2 _ _ hinv7 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 dropping h_v15 hinv7 s7 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__2d.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 h_v16 dropping he_v17 hinv8 e_v17 s8
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2elen.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 h_v16 h_v17 dropping he_v18 hinv9 e_v18 s9
  store_step with Store.apply_rep s10 v18 v8 _ _ hinv10 h64 h_v18 h_v8 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 h_v16 h_v17 dropping h_v18 hinv10 s10 v18
  store_step with Store.apply_rep s11 v17 v19 _ _ hinv11 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 h_v16 dropping h_v17 h_v19 hinv11 s11 v17 v19
  store_step with Store.apply_rep s12 v20 v2 _ _ hinv12 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 h_v16 dropping h_v20 hinv12 s12 v20
  store_step with Store.apply_rep s13 v16 v21 _ _ hinv13 h64 h_v16 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 h_v13 dropping h_v16 h_v21 hinv13 s13 v16 v21
  store_step with Store.apply_rep s14 v13 v22 _ _ hinv14 h64 h_v13 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 dropping h_v13 h_v22 hinv14 s14 v13 v22
  store_step with Store.apply_rep s15 v23 v5 _ _ hinv15 h64 h_v23 h_v5 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v12 dropping h_v23 hinv15 s15 v23
  store_step with Store.apply_rep s16 v12 v24 _ _ hinv16 h64 h_v12 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v12 h_v24 hinv16 s16 v12 v24
  store_step with Store.apply_rep s17 v11 v25 _ _ hinv17 h64 h_v11 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 h_v25 hinv17 s17 v11 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_or.construct s18 e_v27 (by rw [he_v27]; exact empty_args) hinv18 h64 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 dropping he_v27 hinv18 e_v27 s18
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__3e.construct s19 e_v28 (by rw [he_v28]; exact empty_args) hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v27 dropping he_v28 hinv19 e_v28 s19
  store_step with Store.apply_rep s20 v28 v2 _ _ hinv20 h64 h_v28 h_v2 (by ns_tac) (by ns_tac) as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v27 dropping h_v28 hinv20 s20 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2elen.construct s21 e_v30 (by rw [he_v30]; exact empty_args) hinv21 h64 as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v27 h_v29 dropping he_v30 hinv21 e_v30 s21
  store_step with Store.apply_rep s22 v30 v8 _ _ hinv22 h64 h_v30 h_v8 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v27 h_v29 dropping h_v30 hinv22 s22 v30
  store_step with Store.apply_rep s23 v29 v31 _ _ hinv23 h64 h_v29 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v27 dropping h_v29 h_v31 hinv23 s23 v29 v31
  store_step with Store.apply_rep s24 v27 v32 _ _ hinv24 h64 h_v27 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 dropping h_v27 h_v32 hinv24 s24 v27 v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_or.construct s25 e_v34 (by rw [he_v34]; exact empty_args) hinv25 h64 as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 dropping he_v34 hinv25 e_v34 s25
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3e.construct s26 e_v35 (by rw [he_v35]; exact empty_args) hinv26 h64 as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 h_v34 dropping he_v35 hinv26 e_v35 s26
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s27 0#u32 (0) (by scalar_tac) hinv27 h64 as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 h_v34 h_v35 dropping hinv27 s27
  store_step with Store.apply_rep s28 v35 v36 _ _ hinv28 h64 h_v35 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 h_v34 dropping h_v35 h_v36 hinv28 s28 v35 v36
  store_step with Store.apply_rep s29 v37 v2 _ _ hinv29 h64 h_v37 h_v2 (by ns_tac) (by ns_tac) as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 h_v34 dropping h_v37 hinv29 s29 v37
  store_step with Store.apply_rep s30 v34 v38 _ _ hinv30 h64 h_v34 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 dropping h_v34 h_v38 hinv30 s30 v34 v38
  store_step with Store.literal_boolean_spec s31 false hinv31 h64 as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 h_v39 dropping hinv31 s31
  store_step with Store.apply_rep s32 v39 v40 _ _ hinv32 h64 h_v39 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 h_v33 dropping h_v39 h_v40 hinv32 s32 v39 v40
  store_step with Store.apply_rep s33 v33 v41 _ _ hinv33 h64 h_v33 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v26 dropping h_v33 h_v41 hinv33 s33 v33 v41
  store_step with Store.apply_rep s34 v26 v42 _ _ hinv34 h64 h_v26 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v26 h_v42 hinv34 s34 v26 v42
  store_step with Store.apply_rep s35 v10 v43 _ _ hinv35 h64 h_v10 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v43 hinv35 s35 v10 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__3d.construct s36 e_v45 (by rw [he_v45]; exact empty_args) hinv36 h64 as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 dropping he_v45 hinv36 e_v45 s36
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__40purify.construct s37 e_v46 (by rw [he_v46]; exact empty_args) hinv37 h64 as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v45 dropping he_v46 hinv37 e_v46 s37
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s38 e_v47 (by rw [he_v47]; exact empty_args) hinv38 h64 as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v45 h_v46 dropping he_v47 hinv38 e_v47 s38
  store_step with Store.apply_rep s39 v47 v8 _ _ hinv39 h64 h_v47 h_v8 (by ns_tac) (by ns_tac) as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v45 h_v46 dropping h_v47 hinv39 s39 v47
  store_step with Store.apply_rep s40 v48 v5 _ _ hinv40 h64 h_v48 h_v5 (by ns_tac) (by ns_tac) as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v45 h_v46 dropping h_v48 hinv40 s40 v48
  store_step with Store.apply_rep s41 v49 v2 _ _ hinv41 h64 h_v49 h_v2 (by ns_tac) (by ns_tac) as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v45 h_v46 dropping h_v49 hinv41 s41 v49
  store_step with Store.apply_rep s42 v46 v50 _ _ hinv42 h64 h_v46 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v45 dropping h_v46 h_v50 hinv42 s42 v46 v50
  store_step with Store.apply_rep s43 v45 v51 _ _ hinv43 h64 h_v45 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 dropping h_v45 h_v51 hinv43 s43 v45 v51
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s44 1#u32 (-1) (by scalar_tac) hinv44 h64 as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 h_v52 dropping hinv44 s44
  store_step with Store.apply_rep s45 v52 v53 _ _ hinv45 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v44 dropping h_v52 h_v53 hinv45 s45 v52 v53
  store_step with Store.apply_rep s46 v44 v54 _ _ hinv46 h64 h_v44 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v44 h_v54 hinv46 s46 v44 v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_ite.construct s47 e_v56 (by rw [he_v56]; exact empty_args) hinv47 h64 as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 dropping he_v56 hinv47 e_v56 s47
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__3d.construct s48 e_v57 (by rw [he_v57]; exact empty_args) hinv48 h64 as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v56 dropping he_v57 hinv48 e_v57 s48
  store_step with Store.apply_rep s49 v57 v5 _ _ hinv49 h64 h_v57 h_v5 (by ns_tac) (by ns_tac) as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v56 dropping h_v57 hinv49 s49 v57
  store_step with ih.eo__24eo_5ftypeof s50 v8 _ hinv50 h64 (hG.rem hrem) h_v8 as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v56 h_v58 dropping hinv50 s50
  store_step with ih.eo__24seq_5fempty s51 v59 _ hinv51 h64 (hG.rem hrem) h_v59 as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v56 h_v58 dropping h_v59 hinv51 s51 v59
  store_step with Store.apply_mk_rep s52 v58 v60 _ _ hinv52 h64 h_v58 h_v60 as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v56 dropping h_v58 h_v60 hinv52 s52 v58 v60
  store_step with Store.apply_mk_rep s53 v56 v61 _ _ hinv53 h64 h_v56 h_v61 as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 dropping h_v56 h_v61 hinv53 s53 v56 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo__3d.construct s54 e_v63 (by rw [he_v63]; exact empty_args) hinv54 h64 as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 dropping he_v63 hinv54 e_v63 s54
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo__40purify.construct s55 e_v64 (by rw [he_v64]; exact empty_args) hinv55 h64 as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 h_v63 dropping he_v64 hinv55 e_v64 s55
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s56 e_v65 (by rw [he_v65]; exact empty_args) hinv56 h64 as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 h_v63 h_v64 dropping he_v65 hinv56 e_v65 s56
  store_step with Store.apply_rep s57 v65 v8 _ _ hinv57 h64 h_v65 h_v8 (by ns_tac) (by ns_tac) as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 h_v63 h_v64 dropping h_v65 hinv57 s57 v65
  store_step with Store.apply_rep s58 v66 v5 _ _ hinv58 h64 h_v66 h_v5 (by ns_tac) (by ns_tac) as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 h_v63 h_v64 dropping h_v66 hinv58 s58 v66
  store_step with Store.apply_rep s59 v67 v2 _ _ hinv59 h64 h_v67 h_v2 (by ns_tac) (by ns_tac) as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 h_v63 h_v64 dropping h_v67 hinv59 s59 v67
  store_step with Store.apply_rep s60 v64 v68 _ _ hinv60 h64 h_v64 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 h_v63 dropping h_v64 h_v68 hinv60 s60 v64 v68
  store_step with Store.apply_rep s61 v63 v69 _ _ hinv61 h64 h_v63 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 dropping h_v63 h_v69 hinv61 s61 v63 v69
  store_step with Store.apply_rep s62 v70 v2 _ _ hinv62 h64 h_v70 h_v2 (by ns_tac) (by ns_tac) as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v62 dropping h_v70 hinv62 s62 v70
  store_step with Store.apply_mk_rep s63 v62 v71 _ _ hinv63 h64 h_v62 h_v71 as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 dropping h_v62 h_v71 hinv63 s63 v62 v71
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_and.construct s64 e_v73 (by rw [he_v73]; exact empty_args) hinv64 h64 as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 dropping he_v73 hinv64 e_v73 s64
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo__3d.construct s65 e_v74 (by rw [he_v74]; exact empty_args) hinv65 h64 as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 dropping he_v74 hinv65 e_v74 s65
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s66 e_v75 (by rw [he_v75]; exact empty_args) hinv66 h64 as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 dropping he_v75 hinv66 e_v75 s66
  store_step with Store.apply_rep s67 v75 v8 _ _ hinv67 h64 h_v75 h_v8 (by ns_tac) (by ns_tac) as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 dropping h_v75 hinv67 s67 v75
  store_step with Store.apply_rep s68 v76 v2 _ _ hinv68 h64 h_v76 h_v2 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 dropping h_v76 hinv68 s68 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo__2d.construct s69 e_v78 (by rw [he_v78]; exact empty_args) hinv69 h64 as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 h_v77 dropping he_v78 hinv69 e_v78 s69
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_str_2elen.construct s70 e_v79 (by rw [he_v79]; exact empty_args) hinv70 h64 as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 h_v77 h_v78 dropping he_v79 hinv70 e_v79 s70
  store_step with Store.apply_rep s71 v79 v8 _ _ hinv71 h64 h_v79 h_v8 (by ns_tac) (by ns_tac) as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 h_v77 h_v78 dropping h_v79 hinv71 s71 v79
  store_step with Store.apply_rep s72 v78 v80 _ _ hinv72 h64 h_v78 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 h_v77 dropping h_v78 h_v80 hinv72 s72 v78 v80
  store_step with Store.apply_rep s73 v81 v2 _ _ hinv73 h64 h_v81 h_v2 (by ns_tac) (by ns_tac) as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 h_v77 dropping h_v81 hinv73 s73 v81
  store_step with Store.apply_rep s74 v77 v82 _ _ hinv74 h64 h_v77 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v74 dropping h_v77 h_v82 hinv74 s74 v77 v82
  store_step with Store.apply_rep s75 v74 v83 _ _ hinv75 h64 h_v74 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 dropping h_v74 h_v83 hinv75 s75 v74 v83
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s76 e_v85 (by rw [he_v85]; exact empty_args) hinv76 h64 as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 dropping he_v85 hinv76 e_v85 s76
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__40purify.construct s77 e_v86 (by rw [he_v86]; exact empty_args) hinv77 h64 as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 dropping he_v86 hinv77 e_v86 s77
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s78 e_v87 (by rw [he_v87]; exact empty_args) hinv78 h64 as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 dropping he_v87 hinv78 e_v87 s78
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s79 e_v88 (by rw [he_v88]; exact empty_args) hinv79 h64 as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 dropping he_v88 hinv79 e_v88 s79
  store_step with Store.apply_rep s80 v88 v8 _ _ hinv80 h64 h_v88 h_v8 (by ns_tac) (by ns_tac) as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 dropping h_v88 hinv80 s80 v88
  store_step with Store.apply_rep s81 v89 v2 _ _ hinv81 h64 h_v89 h_v2 (by ns_tac) (by ns_tac) as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 dropping h_v89 hinv81 s81 v89
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__2d.construct s82 e_v91 (by rw [he_v91]; exact empty_args) hinv82 h64 as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 h_v90 dropping he_v91 hinv82 e_v91 s82
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_str_2elen.construct s83 e_v92 (by rw [he_v92]; exact empty_args) hinv83 h64 as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 h_v90 h_v91 dropping he_v92 hinv83 e_v92 s83
  store_step with Store.apply_rep s84 v92 v8 _ _ hinv84 h64 h_v92 h_v8 (by ns_tac) (by ns_tac) as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 h_v90 h_v91 dropping h_v92 hinv84 s84 v92
  store_step with Store.apply_rep s85 v91 v93 _ _ hinv85 h64 h_v91 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 h_v90 dropping h_v91 h_v93 hinv85 s85 v91 v93
  store_step with Store.apply_rep s86 v94 v2 _ _ hinv86 h64 h_v94 h_v2 (by ns_tac) (by ns_tac) as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 h_v90 dropping h_v94 hinv86 s86 v94
  store_step with Store.apply_rep s87 v90 v95 _ _ hinv87 h64 h_v90 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v87 dropping h_v90 h_v95 hinv87 s87 v90 v95
  store_step with Store.apply_rep s88 v87 v96 _ _ hinv88 h64 h_v87 h_v96 (by ns_tac) (by ns_tac) as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 dropping h_v87 h_v96 hinv88 s88 v87 v96
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s89 0#u32 (0) (by scalar_tac) hinv89 h64 as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v97 dropping hinv89 s89
  store_step with Store.apply_rep s90 v97 v98 _ _ hinv90 h64 h_v97 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 dropping h_v97 h_v98 hinv90 s90 v97 v98
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s91 e_v100 (by rw [he_v100]; exact empty_args) hinv91 h64 as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 dropping he_v100 hinv91 e_v100 s91
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s92 e_v101 (by rw [he_v101]; exact empty_args) hinv92 h64 as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 dropping he_v101 hinv92 e_v101 s92
  store_step with Store.apply_rep s93 v101 v8 _ _ hinv93 h64 h_v101 h_v8 (by ns_tac) (by ns_tac) as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 dropping h_v101 hinv93 s93 v101
  store_step with Store.apply_rep s94 v102 v2 _ _ hinv94 h64 h_v102 h_v2 (by ns_tac) (by ns_tac) as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 dropping h_v102 hinv94 s94 v102
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo__2d.construct s95 e_v104 (by rw [he_v104]; exact empty_args) hinv95 h64 as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 h_v103 dropping he_v104 hinv95 e_v104 s95
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo_str_2elen.construct s96 e_v105 (by rw [he_v105]; exact empty_args) hinv96 h64 as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 h_v103 h_v104 dropping he_v105 hinv96 e_v105 s96
  store_step with Store.apply_rep s97 v105 v8 _ _ hinv97 h64 h_v105 h_v8 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 h_v103 h_v104 dropping h_v105 hinv97 s97 v105
  store_step with Store.apply_rep s98 v104 v106 _ _ hinv98 h64 h_v104 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 h_v103 dropping h_v104 h_v106 hinv98 s98 v104 v106
  store_step with Store.apply_rep s99 v107 v2 _ _ hinv99 h64 h_v107 h_v2 (by ns_tac) (by ns_tac) as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 h_v103 dropping h_v107 hinv99 s99 v107
  store_step with Store.apply_rep s100 v103 v108 _ _ hinv100 h64 h_v103 h_v108 (by ns_tac) (by ns_tac) as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v100 dropping h_v103 h_v108 hinv100 s100 v103 v108
  store_step with Store.apply_rep s101 v100 v109 _ _ hinv101 h64 h_v100 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 dropping h_v100 h_v109 hinv101 s101 v100 v109
  store_step with Store.apply_rep s102 v110 v5 _ _ hinv102 h64 h_v110 h_v5 (by ns_tac) (by ns_tac) as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 dropping h_v110 hinv102 s102 v110
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s103 0#u32 (0) (by scalar_tac) hinv103 h64 as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 h_v111 dropping hinv103 s103
  store_step with Store.apply_rep s104 v111 v112 _ _ hinv104 h64 h_v111 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 h_v99 dropping h_v111 h_v112 hinv104 s104 v111 v112
  store_step with Store.apply_rep s105 v99 v113 _ _ hinv105 h64 h_v99 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 h_v86 dropping h_v113 h_v99 hinv105 s105 v113 v99
  store_step with Store.apply_rep s106 v86 v114 _ _ hinv106 h64 h_v86 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v85 dropping h_v114 h_v86 hinv106 s106 v114 v86
  store_step with Store.apply_rep s107 v85 v115 _ _ hinv107 h64 h_v85 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 dropping h_v115 h_v85 hinv107 s107 v115 v85
  step as ⟨e_v117, he_v117⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s108 e_v117 (by rw [he_v117]; exact empty_args) hinv108 h64 as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 dropping he_v117 hinv108 e_v117 s108
  store_step with Store.apply_rep s109 v117 v5 _ _ hinv109 h64 h_v117 h_v5 (by ns_tac) (by ns_tac) as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 dropping h_v117 hinv109 s109 v117
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s110 e_v119 (by rw [he_v119]; exact empty_args) hinv110 h64 as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 dropping he_v119 hinv110 e_v119 s110
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__40purify.construct s111 e_v120 (by rw [he_v120]; exact empty_args) hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 dropping he_v120 hinv111 e_v120 s111
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s112 e_v121 (by rw [he_v121]; exact empty_args) hinv112 h64 as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 dropping he_v121 hinv112 e_v121 s112
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s113 e_v122 (by rw [he_v122]; exact empty_args) hinv113 h64 as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 dropping he_v122 hinv113 e_v122 s113
  store_step with Store.apply_rep s114 v122 v8 _ _ hinv114 h64 h_v122 h_v8 (by ns_tac) (by ns_tac) as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 dropping h_v122 hinv114 s114 v122
  store_step with Store.apply_rep s115 v123 v2 _ _ hinv115 h64 h_v123 h_v2 (by ns_tac) (by ns_tac) as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 dropping h_v123 hinv115 s115 v123
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo__2d.construct s116 e_v125 (by rw [he_v125]; exact empty_args) hinv116 h64 as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 h_v124 dropping he_v125 hinv116 e_v125 s116
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo_str_2elen.construct s117 e_v126 (by rw [he_v126]; exact empty_args) hinv117 h64 as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 h_v124 h_v125 dropping he_v126 hinv117 e_v126 s117
  store_step with Store.apply_rep s118 v126 v8 _ _ hinv118 h64 h_v126 h_v8 (by ns_tac) (by ns_tac) as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 h_v124 h_v125 dropping h_v126 hinv118 s118 v126
  store_step with Store.apply_rep s119 v125 v127 _ _ hinv119 h64 h_v125 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 h_v124 dropping h_v125 h_v127 hinv119 s119 v125 v127
  store_step with Store.apply_rep s120 v128 v2 _ _ hinv120 h64 h_v128 h_v2 (by ns_tac) (by ns_tac) as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 h_v124 dropping h_v128 hinv120 s120 v128
  store_step with Store.apply_rep s121 v124 v129 _ _ hinv121 h64 h_v124 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v121 dropping h_v124 h_v129 hinv121 s121 v124 v129
  store_step with Store.apply_rep s122 v121 v130 _ _ hinv122 h64 h_v121 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 dropping h_v121 h_v130 hinv122 s122 v121 v130
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo__2b.construct s123 e_v132 (by rw [he_v132]; exact empty_args) hinv123 h64 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 dropping he_v132 hinv123 e_v132 s123
  step as ⟨e_v133, he_v133⟩
  store_step with CtorSpec.eo_str_2elen.construct s124 e_v133 (by rw [he_v133]; exact empty_args) hinv124 h64 as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 dropping he_v133 hinv124 e_v133 s124
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo__40purify.construct s125 e_v134 (by rw [he_v134]; exact empty_args) hinv125 h64 as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 dropping he_v134 hinv125 e_v134 s125
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s126 e_v135 (by rw [he_v135]; exact empty_args) hinv126 h64 as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 dropping he_v135 hinv126 e_v135 s126
  step as ⟨e_v136, he_v136⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s127 e_v136 (by rw [he_v136]; exact empty_args) hinv127 h64 as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 dropping he_v136 hinv127 e_v136 s127
  store_step with Store.apply_rep s128 v136 v8 _ _ hinv128 h64 h_v136 h_v8 (by ns_tac) (by ns_tac) as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 dropping h_v136 hinv128 s128 v136
  store_step with Store.apply_rep s129 v137 v2 _ _ hinv129 h64 h_v137 h_v2 (by ns_tac) (by ns_tac) as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 dropping h_v137 hinv129 s129 v137
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo__2d.construct s130 e_v139 (by rw [he_v139]; exact empty_args) hinv130 h64 as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 h_v138 dropping he_v139 hinv130 e_v139 s130
  step as ⟨e_v140, he_v140⟩
  store_step with CtorSpec.eo_str_2elen.construct s131 e_v140 (by rw [he_v140]; exact empty_args) hinv131 h64 as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 h_v138 h_v139 dropping he_v140 hinv131 e_v140 s131
  store_step with Store.apply_rep s132 v140 v8 _ _ hinv132 h64 h_v140 h_v8 (by ns_tac) (by ns_tac) as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 h_v138 h_v139 dropping h_v140 hinv132 s132 v140
  store_step with Store.apply_rep s133 v139 v141 _ _ hinv133 h64 h_v139 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 h_v138 dropping h_v139 h_v141 hinv133 s133 v139 v141
  store_step with Store.apply_rep s134 v142 v2 _ _ hinv134 h64 h_v142 h_v2 (by ns_tac) (by ns_tac) as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 h_v138 dropping h_v142 hinv134 s134 v142
  store_step with Store.apply_rep s135 v138 v143 _ _ hinv135 h64 h_v138 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v135 dropping h_v138 h_v143 hinv135 s135 v138 v143
  store_step with Store.apply_rep s136 v135 v144 _ _ hinv136 h64 h_v135 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 dropping h_v135 h_v144 hinv136 s136 v135 v144
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s137 0#u32 (0) (by scalar_tac) hinv137 h64 as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v145 dropping hinv137 s137
  store_step with Store.apply_rep s138 v145 v146 _ _ hinv138 h64 h_v145 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 dropping h_v145 h_v146 hinv138 s138 v145 v146
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s139 e_v148 (by rw [he_v148]; exact empty_args) hinv139 h64 as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 dropping he_v148 hinv139 e_v148 s139
  step as ⟨e_v149, he_v149⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s140 e_v149 (by rw [he_v149]; exact empty_args) hinv140 h64 as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 dropping he_v149 hinv140 e_v149 s140
  store_step with Store.apply_rep s141 v149 v8 _ _ hinv141 h64 h_v149 h_v8 (by ns_tac) (by ns_tac) as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 dropping h_v149 hinv141 s141 v149
  store_step with Store.apply_rep s142 v150 v2 _ _ hinv142 h64 h_v150 h_v2 (by ns_tac) (by ns_tac) as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 dropping h_v150 hinv142 s142 v150
  step as ⟨e_v152, he_v152⟩
  store_step with CtorSpec.eo__2d.construct s143 e_v152 (by rw [he_v152]; exact empty_args) hinv143 h64 as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 h_v151 dropping he_v152 hinv143 e_v152 s143
  step as ⟨e_v153, he_v153⟩
  store_step with CtorSpec.eo_str_2elen.construct s144 e_v153 (by rw [he_v153]; exact empty_args) hinv144 h64 as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 h_v151 h_v152 dropping he_v153 hinv144 e_v153 s144
  store_step with Store.apply_rep s145 v153 v8 _ _ hinv145 h64 h_v153 h_v8 (by ns_tac) (by ns_tac) as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 h_v151 h_v152 dropping h_v153 hinv145 s145 v153
  store_step with Store.apply_rep s146 v152 v154 _ _ hinv146 h64 h_v152 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 h_v151 dropping h_v152 h_v154 hinv146 s146 v152 v154
  store_step with Store.apply_rep s147 v155 v2 _ _ hinv147 h64 h_v155 h_v2 (by ns_tac) (by ns_tac) as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 h_v151 dropping h_v155 hinv147 s147 v155
  store_step with Store.apply_rep s148 v151 v156 _ _ hinv148 h64 h_v151 h_v156 (by ns_tac) (by ns_tac) as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v148 dropping h_v151 h_v156 hinv148 s148 v151 v156
  store_step with Store.apply_rep s149 v148 v157 _ _ hinv149 h64 h_v148 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 dropping h_v148 h_v157 hinv149 s149 v148 v157
  store_step with Store.apply_rep s150 v158 v5 _ _ hinv150 h64 h_v158 h_v5 (by ns_tac) (by ns_tac) as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 dropping h_v158 hinv150 s150 v158
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s151 0#u32 (0) (by scalar_tac) hinv151 h64 as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 h_v159 dropping hinv151 s151
  store_step with Store.apply_rep s152 v159 v160 _ _ hinv152 h64 h_v159 h_v160 (by ns_tac) (by ns_tac) as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 h_v147 dropping h_v159 h_v160 hinv152 s152 v159 v160
  store_step with Store.apply_rep s153 v147 v161 _ _ hinv153 h64 h_v147 h_v161 (by ns_tac) (by ns_tac) as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 h_v134 dropping h_v147 h_v161 hinv153 s153 v147 v161
  store_step with Store.apply_rep s154 v134 v162 _ _ hinv154 h64 h_v134 h_v162 (by ns_tac) (by ns_tac) as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 h_v133 dropping h_v134 h_v162 hinv154 s154 v134 v162
  store_step with Store.apply_rep s155 v133 v163 _ _ hinv155 h64 h_v133 h_v163 (by ns_tac) (by ns_tac) as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v132 dropping h_v133 h_v163 hinv155 s155 v133 v163
  store_step with Store.apply_rep s156 v132 v164 _ _ hinv156 h64 h_v132 h_v164 (by ns_tac) (by ns_tac) as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 dropping h_v132 h_v164 hinv156 s156 v132 v164
  step as ⟨e_v166, he_v166⟩
  store_step with CtorSpec.eo__2b.construct s157 e_v166 (by rw [he_v166]; exact empty_args) hinv157 h64 as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v165 dropping he_v166 hinv157 e_v166 s157
  step as ⟨e_v167, he_v167⟩
  store_step with CtorSpec.eo_str_2elen.construct s158 e_v167 (by rw [he_v167]; exact empty_args) hinv158 h64 as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v165 h_v166 dropping he_v167 hinv158 e_v167 s158
  store_step with Store.apply_rep s159 v167 v5 _ _ hinv159 h64 h_v167 h_v5 (by ns_tac) (by ns_tac) as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v165 h_v166 dropping h_v167 hinv159 s159 v167
  store_step with Store.apply_rep s160 v166 v168 _ _ hinv160 h64 h_v166 h_v168 (by ns_tac) (by ns_tac) as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v165 dropping h_v166 h_v168 hinv160 s160 v166 v168
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s161 0#u32 (0) (by scalar_tac) hinv161 h64 as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v165 h_v169 dropping hinv161 s161
  store_step with Store.apply_rep s162 v169 v170 _ _ hinv162 h64 h_v169 h_v170 (by ns_tac) (by ns_tac) as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 h_v165 dropping h_v169 h_v170 hinv162 s162 v169 v170
  store_step with Store.apply_rep s163 v165 v171 _ _ hinv163 h64 h_v165 h_v171 (by ns_tac) (by ns_tac) as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v131 dropping h_v165 h_v171 hinv163 s163 v165 v171
  store_step with Store.apply_rep s164 v131 v172 _ _ hinv164 h64 h_v131 h_v172 (by ns_tac) (by ns_tac) as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 dropping h_v131 h_v172 hinv164 s164 v131 v172
  step as ⟨e_v174, he_v174⟩
  store_step with CtorSpec.eo__2d.construct s165 e_v174 (by rw [he_v174]; exact empty_args) hinv165 h64 as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 dropping he_v174 hinv165 e_v174 s165
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo_str_2elen.construct s166 e_v175 (by rw [he_v175]; exact empty_args) hinv166 h64 as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 dropping he_v175 hinv166 e_v175 s166
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s167 e_v176 (by rw [he_v176]; exact empty_args) hinv167 h64 as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 dropping he_v176 hinv167 e_v176 s167
  store_step with Store.apply_rep s168 v176 v8 _ _ hinv168 h64 h_v176 h_v8 (by ns_tac) (by ns_tac) as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 dropping h_v176 hinv168 s168 v176
  store_step with Store.apply_rep s169 v177 v2 _ _ hinv169 h64 h_v177 h_v2 (by ns_tac) (by ns_tac) as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 dropping h_v177 hinv169 s169 v177
  step as ⟨e_v179, he_v179⟩
  store_step with CtorSpec.eo__2d.construct s170 e_v179 (by rw [he_v179]; exact empty_args) hinv170 h64 as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 h_v178 dropping he_v179 hinv170 e_v179 s170
  step as ⟨e_v180, he_v180⟩
  store_step with CtorSpec.eo_str_2elen.construct s171 e_v180 (by rw [he_v180]; exact empty_args) hinv171 h64 as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 h_v178 h_v179 dropping he_v180 hinv171 e_v180 s171
  store_step with Store.apply_rep s172 v180 v8 _ _ hinv172 h64 h_v180 h_v8 (by ns_tac) (by ns_tac) as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 h_v178 h_v179 dropping h_v180 hinv172 s172 v180
  store_step with Store.apply_rep s173 v179 v181 _ _ hinv173 h64 h_v179 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 h_v178 dropping h_v179 h_v181 hinv173 s173 v179 v181
  store_step with Store.apply_rep s174 v182 v2 _ _ hinv174 h64 h_v182 h_v2 (by ns_tac) (by ns_tac) as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 h_v178 dropping h_v182 hinv174 s174 v182
  store_step with Store.apply_rep s175 v178 v183 _ _ hinv175 h64 h_v178 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 h_v175 dropping h_v178 h_v183 hinv175 s175 v178 v183
  store_step with Store.apply_rep s176 v175 v184 _ _ hinv176 h64 h_v175 h_v184 (by ns_tac) (by ns_tac) as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v174 dropping h_v175 h_v184 hinv176 s176 v175 v184
  store_step with Store.apply_rep s177 v174 v185 _ _ hinv177 h64 h_v174 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 dropping h_v174 h_v185 hinv177 s177 v174 v185
  step as ⟨e_v187, he_v187⟩
  store_step with CtorSpec.eo__2b.construct s178 e_v187 (by rw [he_v187]; exact empty_args) hinv178 h64 as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 dropping he_v187 hinv178 e_v187 s178
  step as ⟨e_v188, he_v188⟩
  store_step with CtorSpec.eo_str_2elen.construct s179 e_v188 (by rw [he_v188]; exact empty_args) hinv179 h64 as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 dropping he_v188 hinv179 e_v188 s179
  step as ⟨e_v189, he_v189⟩
  store_step with CtorSpec.eo__40purify.construct s180 e_v189 (by rw [he_v189]; exact empty_args) hinv180 h64 as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 dropping he_v189 hinv180 e_v189 s180
  step as ⟨e_v190, he_v190⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s181 e_v190 (by rw [he_v190]; exact empty_args) hinv181 h64 as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 dropping he_v190 hinv181 e_v190 s181
  step as ⟨e_v191, he_v191⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s182 e_v191 (by rw [he_v191]; exact empty_args) hinv182 h64 as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 dropping he_v191 hinv182 e_v191 s182
  store_step with Store.apply_rep s183 v191 v8 _ _ hinv183 h64 h_v191 h_v8 (by ns_tac) (by ns_tac) as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 dropping h_v191 hinv183 s183 v191
  store_step with Store.apply_rep s184 v192 v2 _ _ hinv184 h64 h_v192 h_v2 (by ns_tac) (by ns_tac) as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 dropping h_v192 hinv184 s184 v192
  step as ⟨e_v194, he_v194⟩
  store_step with CtorSpec.eo__2d.construct s185 e_v194 (by rw [he_v194]; exact empty_args) hinv185 h64 as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 h_v193 dropping he_v194 hinv185 e_v194 s185
  step as ⟨e_v195, he_v195⟩
  store_step with CtorSpec.eo_str_2elen.construct s186 e_v195 (by rw [he_v195]; exact empty_args) hinv186 h64 as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 h_v193 h_v194 dropping he_v195 hinv186 e_v195 s186
  store_step with Store.apply_rep s187 v195 v8 _ _ hinv187 h64 h_v195 h_v8 (by ns_tac) (by ns_tac) as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 h_v193 h_v194 dropping h_v195 hinv187 s187 v195
  store_step with Store.apply_rep s188 v194 v196 _ _ hinv188 h64 h_v194 h_v196 (by ns_tac) (by ns_tac) as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 h_v193 dropping h_v194 h_v196 hinv188 s188 v194 v196
  store_step with Store.apply_rep s189 v197 v2 _ _ hinv189 h64 h_v197 h_v2 (by ns_tac) (by ns_tac) as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 h_v193 dropping h_v197 hinv189 s189 v197
  store_step with Store.apply_rep s190 v193 v198 _ _ hinv190 h64 h_v193 h_v198 (by ns_tac) (by ns_tac) as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v190 dropping h_v193 h_v198 hinv190 s190 v193 v198
  store_step with Store.apply_rep s191 v190 v199 _ _ hinv191 h64 h_v190 h_v199 (by ns_tac) (by ns_tac) as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 dropping h_v190 h_v199 hinv191 s191 v190 v199
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s192 0#u32 (0) (by scalar_tac) hinv192 h64 as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v200 dropping hinv192 s192
  store_step with Store.apply_rep s193 v200 v201 _ _ hinv193 h64 h_v200 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 dropping h_v200 h_v201 hinv193 s193 v200 v201
  step as ⟨e_v203, he_v203⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s194 e_v203 (by rw [he_v203]; exact empty_args) hinv194 h64 as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 dropping he_v203 hinv194 e_v203 s194
  step as ⟨e_v204, he_v204⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s195 e_v204 (by rw [he_v204]; exact empty_args) hinv195 h64 as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 dropping he_v204 hinv195 e_v204 s195
  store_step with Store.apply_rep s196 v204 v8 _ _ hinv196 h64 h_v204 h_v8 (by ns_tac) (by ns_tac) as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 dropping h_v204 hinv196 s196 v204
  store_step with Store.apply_rep s197 v205 v2 _ _ hinv197 h64 h_v205 h_v2 (by ns_tac) (by ns_tac) as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 dropping h_v205 hinv197 s197 v205
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo__2d.construct s198 e_v207 (by rw [he_v207]; exact empty_args) hinv198 h64 as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 h_v206 dropping he_v207 hinv198 e_v207 s198
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo_str_2elen.construct s199 e_v208 (by rw [he_v208]; exact empty_args) hinv199 h64 as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 h_v206 h_v207 dropping he_v208 hinv199 e_v208 s199
  store_step with Store.apply_rep s200 v208 v8 _ _ hinv200 h64 h_v208 h_v8 (by ns_tac) (by ns_tac) as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 h_v206 h_v207 dropping h_v208 hinv200 s200 v208
  store_step with Store.apply_rep s201 v207 v209 _ _ hinv201 h64 h_v207 h_v209 (by ns_tac) (by ns_tac) as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 h_v206 dropping h_v207 h_v209 hinv201 s201 v207 v209
  store_step with Store.apply_rep s202 v210 v2 _ _ hinv202 h64 h_v210 h_v2 (by ns_tac) (by ns_tac) as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 h_v206 dropping h_v210 hinv202 s202 v210
  store_step with Store.apply_rep s203 v206 v211 _ _ hinv203 h64 h_v206 h_v211 (by ns_tac) (by ns_tac) as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v203 dropping h_v206 h_v211 hinv203 s203 v206 v211
  store_step with Store.apply_rep s204 v203 v212 _ _ hinv204 h64 h_v203 h_v212 (by ns_tac) (by ns_tac) as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 dropping h_v203 h_v212 hinv204 s204 v203 v212
  store_step with Store.apply_rep s205 v213 v5 _ _ hinv205 h64 h_v213 h_v5 (by ns_tac) (by ns_tac) as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 dropping h_v213 hinv205 s205 v213
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s206 0#u32 (0) (by scalar_tac) hinv206 h64 as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 h_v214 dropping hinv206 s206
  store_step with Store.apply_rep s207 v214 v215 _ _ hinv207 h64 h_v214 h_v215 (by ns_tac) (by ns_tac) as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 h_v202 dropping h_v214 h_v215 hinv207 s207 v214 v215
  store_step with Store.apply_rep s208 v202 v216 _ _ hinv208 h64 h_v202 h_v216 (by ns_tac) (by ns_tac) as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 h_v189 dropping h_v202 h_v216 hinv208 s208 v202 v216
  store_step with Store.apply_rep s209 v189 v217 _ _ hinv209 h64 h_v189 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 h_v188 dropping h_v189 h_v217 hinv209 s209 v189 v217
  store_step with Store.apply_rep s210 v188 v218 _ _ hinv210 h64 h_v188 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v187 dropping h_v188 h_v218 hinv210 s210 v188 v218
  store_step with Store.apply_rep s211 v187 v219 _ _ hinv211 h64 h_v187 h_v219 (by ns_tac) (by ns_tac) as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 dropping h_v187 h_v219 hinv211 s211 v187 v219
  step as ⟨e_v221, he_v221⟩
  store_step with CtorSpec.eo__2b.construct s212 e_v221 (by rw [he_v221]; exact empty_args) hinv212 h64 as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v220 dropping he_v221 hinv212 e_v221 s212
  step as ⟨e_v222, he_v222⟩
  store_step with CtorSpec.eo_str_2elen.construct s213 e_v222 (by rw [he_v222]; exact empty_args) hinv213 h64 as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v220 h_v221 dropping he_v222 hinv213 e_v222 s213
  store_step with Store.apply_rep s214 v222 v5 _ _ hinv214 h64 h_v222 h_v5 (by ns_tac) (by ns_tac) as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v220 h_v221 dropping h_v222 hinv214 s214 v222
  store_step with Store.apply_rep s215 v221 v223 _ _ hinv215 h64 h_v221 h_v223 (by ns_tac) (by ns_tac) as ⟨v224, s216, hinv216, h_v224⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v220 dropping h_v221 h_v223 hinv215 s215 v221 v223
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s216 0#u32 (0) (by scalar_tac) hinv216 h64 as ⟨v225, s217, hinv217, h_v225⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v220 h_v224 dropping hinv216 s216
  store_step with Store.apply_rep s217 v224 v225 _ _ hinv217 h64 h_v224 h_v225 (by ns_tac) (by ns_tac) as ⟨v226, s218, hinv218, h_v226⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 h_v220 dropping h_v224 h_v225 hinv217 s217 v224 v225
  store_step with Store.apply_rep s218 v220 v226 _ _ hinv218 h64 h_v220 h_v226 (by ns_tac) (by ns_tac) as ⟨v227, s219, hinv219, h_v227⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 h_v186 dropping h_v220 h_v226 hinv218 s218 v220 v226
  store_step with Store.apply_rep s219 v186 v227 _ _ hinv219 h64 h_v186 h_v227 (by ns_tac) (by ns_tac) as ⟨v228, s220, hinv220, h_v228⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 h_v173 dropping h_v186 h_v227 hinv219 s219 v186 v227
  store_step with Store.apply_rep s220 v173 v228 _ _ hinv220 h64 h_v173 h_v228 (by ns_tac) (by ns_tac) as ⟨v229, s221, hinv221, h_v229⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 h_v120 dropping h_v173 h_v228 hinv220 s220 v173 v228
  store_step with Store.apply_rep s221 v120 v229 _ _ hinv221 h64 h_v120 h_v229 (by ns_tac) (by ns_tac) as ⟨v230, s222, hinv222, h_v230⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v119 dropping h_v120 h_v229 hinv221 s221 v120 v229
  store_step with Store.apply_rep s222 v119 v230 _ _ hinv222 h64 h_v119 h_v230 (by ns_tac) (by ns_tac) as ⟨v231, s223, hinv223, h_v231⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 dropping h_v119 h_v230 hinv222 s222 v119 v230
  step as ⟨e_v232, he_v232⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s223 e_v232 (by rw [he_v232]; exact empty_args) hinv223 h64 as ⟨v232, s224, hinv224, h_v232⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 dropping he_v232 hinv223 e_v232 s223
  step as ⟨e_v233, he_v233⟩
  store_step with CtorSpec.eo__40purify.construct s224 e_v233 (by rw [he_v233]; exact empty_args) hinv224 h64 as ⟨v233, s225, hinv225, h_v233⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 dropping he_v233 hinv224 e_v233 s224
  step as ⟨e_v234, he_v234⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s225 e_v234 (by rw [he_v234]; exact empty_args) hinv225 h64 as ⟨v234, s226, hinv226, h_v234⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 dropping he_v234 hinv225 e_v234 s225
  step as ⟨e_v235, he_v235⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s226 e_v235 (by rw [he_v235]; exact empty_args) hinv226 h64 as ⟨v235, s227, hinv227, h_v235⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 dropping he_v235 hinv226 e_v235 s226
  store_step with Store.apply_rep s227 v235 v8 _ _ hinv227 h64 h_v235 h_v8 (by ns_tac) (by ns_tac) as ⟨v236, s228, hinv228, h_v236⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 dropping h_v235 hinv227 s227 v235
  store_step with Store.apply_rep s228 v236 v2 _ _ hinv228 h64 h_v236 h_v2 (by ns_tac) (by ns_tac) as ⟨v237, s229, hinv229, h_v237⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 dropping h_v236 hinv228 s228 v236
  step as ⟨e_v238, he_v238⟩
  store_step with CtorSpec.eo__2d.construct s229 e_v238 (by rw [he_v238]; exact empty_args) hinv229 h64 as ⟨v238, s230, hinv230, h_v238⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 h_v237 dropping he_v238 hinv229 e_v238 s229
  step as ⟨e_v239, he_v239⟩
  store_step with CtorSpec.eo_str_2elen.construct s230 e_v239 (by rw [he_v239]; exact empty_args) hinv230 h64 as ⟨v239, s231, hinv231, h_v239⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 h_v237 h_v238 dropping he_v239 hinv230 e_v239 s230
  store_step with Store.apply_rep s231 v239 v8 _ _ hinv231 h64 h_v239 h_v8 (by ns_tac) (by ns_tac) as ⟨v240, s232, hinv232, h_v240⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 h_v237 h_v238 dropping h_v239 hinv231 s231 v239
  store_step with Store.apply_rep s232 v238 v240 _ _ hinv232 h64 h_v238 h_v240 (by ns_tac) (by ns_tac) as ⟨v241, s233, hinv233, h_v241⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 h_v237 dropping h_v238 h_v240 hinv232 s232 v238 v240
  store_step with Store.apply_rep s233 v241 v2 _ _ hinv233 h64 h_v241 h_v2 (by ns_tac) (by ns_tac) as ⟨v242, s234, hinv234, h_v242⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 h_v237 dropping h_v241 hinv233 s233 v241
  store_step with Store.apply_rep s234 v237 v242 _ _ hinv234 h64 h_v237 h_v242 (by ns_tac) (by ns_tac) as ⟨v243, s235, hinv235, h_v243⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v234 dropping h_v237 h_v242 hinv234 s234 v237 v242
  store_step with Store.apply_rep s235 v234 v243 _ _ hinv235 h64 h_v234 h_v243 (by ns_tac) (by ns_tac) as ⟨v244, s236, hinv236, h_v244⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 dropping h_v234 h_v243 hinv235 s235 v234 v243
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s236 0#u32 (0) (by scalar_tac) hinv236 h64 as ⟨v245, s237, hinv237, h_v245⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v244 dropping hinv236 s236
  store_step with Store.apply_rep s237 v244 v245 _ _ hinv237 h64 h_v244 h_v245 (by ns_tac) (by ns_tac) as ⟨v246, s238, hinv238, h_v246⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 dropping h_v244 h_v245 hinv237 s237 v244 v245
  step as ⟨e_v247, he_v247⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s238 e_v247 (by rw [he_v247]; exact empty_args) hinv238 h64 as ⟨v247, s239, hinv239, h_v247⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 dropping he_v247 hinv238 e_v247 s238
  step as ⟨e_v248, he_v248⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s239 e_v248 (by rw [he_v248]; exact empty_args) hinv239 h64 as ⟨v248, s240, hinv240, h_v248⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 dropping he_v248 hinv239 e_v248 s239
  store_step with Store.apply_rep s240 v248 v8 _ _ hinv240 h64 h_v248 h_v8 (by ns_tac) (by ns_tac) as ⟨v249, s241, hinv241, h_v249⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 dropping h_v248 hinv240 s240 v248
  store_step with Store.apply_rep s241 v249 v2 _ _ hinv241 h64 h_v249 h_v2 (by ns_tac) (by ns_tac) as ⟨v250, s242, hinv242, h_v250⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 dropping h_v249 hinv241 s241 v249
  step as ⟨e_v251, he_v251⟩
  store_step with CtorSpec.eo__2d.construct s242 e_v251 (by rw [he_v251]; exact empty_args) hinv242 h64 as ⟨v251, s243, hinv243, h_v251⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 h_v250 dropping he_v251 hinv242 e_v251 s242
  step as ⟨e_v252, he_v252⟩
  store_step with CtorSpec.eo_str_2elen.construct s243 e_v252 (by rw [he_v252]; exact empty_args) hinv243 h64 as ⟨v252, s244, hinv244, h_v252⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 h_v250 h_v251 dropping he_v252 hinv243 e_v252 s243
  store_step with Store.apply_rep s244 v252 v8 _ _ hinv244 h64 h_v252 h_v8 (by ns_tac) (by ns_tac) as ⟨v253, s245, hinv245, h_v253⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 h_v250 h_v251 dropping h_v252 hinv244 s244 v252
  store_step with Store.apply_rep s245 v251 v253 _ _ hinv245 h64 h_v251 h_v253 (by ns_tac) (by ns_tac) as ⟨v254, s246, hinv246, h_v254⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 h_v250 dropping h_v251 h_v253 hinv245 s245 v251 v253
  store_step with Store.apply_rep s246 v254 v2 _ _ hinv246 h64 h_v254 h_v2 (by ns_tac) (by ns_tac) as ⟨v255, s247, hinv247, h_v255⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 h_v250 dropping h_v254 hinv246 s246 v254
  store_step with Store.apply_rep s247 v250 v255 _ _ hinv247 h64 h_v250 h_v255 (by ns_tac) (by ns_tac) as ⟨v256, s248, hinv248, h_v256⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v247 dropping h_v250 h_v255 hinv247 s247 v250 v255
  store_step with Store.apply_rep s248 v247 v256 _ _ hinv248 h64 h_v247 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s249, hinv249, h_v257⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 dropping h_v247 h_v256 hinv248 s248 v247 v256
  store_step with Store.apply_rep s249 v257 v5 _ _ hinv249 h64 h_v257 h_v5 (by ns_tac) (by ns_tac) as ⟨v258, s250, hinv250, h_v258⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 dropping h_v257 hinv249 s249 v257
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s250 0#u32 (0) (by scalar_tac) hinv250 h64 as ⟨v259, s251, hinv251, h_v259⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 h_v258 dropping hinv250 s250
  store_step with Store.apply_rep s251 v258 v259 _ _ hinv251 h64 h_v258 h_v259 (by ns_tac) (by ns_tac) as ⟨v260, s252, hinv252, h_v260⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 h_v246 dropping h_v258 h_v259 hinv251 s251 v258 v259
  store_step with Store.apply_rep s252 v246 v260 _ _ hinv252 h64 h_v246 h_v260 (by ns_tac) (by ns_tac) as ⟨v261, s253, hinv253, h_v261⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 h_v233 dropping h_v246 h_v260 hinv252 s252 v246 v260
  store_step with Store.apply_rep s253 v233 v261 _ _ hinv253 h64 h_v233 h_v261 (by ns_tac) (by ns_tac) as ⟨v262, s254, hinv254, h_v262⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 dropping h_v233 h_v261 hinv253 s253 v233 v261
  store_step with ih.eo__24eo_5ftypeof s254 v262 _ hinv254 h64 (hG.rem hrem) h_v262 as ⟨v263, s255, hinv255, h_v263⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 h_v232 dropping h_v262 hinv254 s254 v262
  store_step with ih.eo__24eo_5fnil s255 v232 v263 _ _ hinv255 h64 (hG.rem hrem) h_v232 h_v263 as ⟨v264, s256, hinv256, h_v264⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 h_v231 dropping h_v232 h_v263 hinv255 s255 v232 v263
  store_step with Store.apply_mk_rep s256 v231 v264 _ _ hinv256 h64 h_v231 h_v264 as ⟨v265, s257, hinv257, h_v265⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 h_v118 dropping h_v231 h_v264 hinv256 s256 v231 v264
  store_step with Store.apply_mk_rep s257 v118 v265 _ _ hinv257 h64 h_v118 h_v265 as ⟨v266, s258, hinv258, h_v266⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 h_v116 dropping h_v118 h_v265 hinv257 s257 v118 v265
  store_step with Store.apply_mk_rep s258 v116 v266 _ _ hinv258 h64 h_v116 h_v266 as ⟨v267, s259, hinv259, h_v267⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 h_v84 dropping h_v116 h_v266 hinv258 s258 v116 v266
  store_step with Store.apply_mk_rep s259 v84 v267 _ _ hinv259 h64 h_v84 h_v267 as ⟨v268, s260, hinv260, h_v268⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v73 dropping h_v267 h_v84 hinv259 s259 v267 v84
  store_step with Store.apply_mk_rep s260 v73 v268 _ _ hinv260 h64 h_v73 h_v268 as ⟨v269, s261, hinv261, h_v269⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 dropping h_v268 h_v73 hinv260 s260 v268 v73
  step as ⟨e_v270, he_v270⟩
  store_step with CtorSpec.eo_and.construct s261 e_v270 (by rw [he_v270]; exact empty_args) hinv261 h64 as ⟨v270, s262, hinv262, h_v270⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 dropping he_v270 hinv261 e_v270 s261
  step as ⟨e_v271, he_v271⟩
  store_step with CtorSpec.eo_not.construct s262 e_v271 (by rw [he_v271]; exact empty_args) hinv262 h64 as ⟨v271, s263, hinv263, h_v271⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 dropping he_v271 hinv262 e_v271 s262
  step as ⟨e_v272, he_v272⟩
  store_step with CtorSpec.eo_str_2econtains.construct s263 e_v272 (by rw [he_v272]; exact empty_args) hinv263 h64 as ⟨v272, s264, hinv264, h_v272⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 dropping he_v272 hinv263 e_v272 s263
  step as ⟨e_v273, he_v273⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s264 e_v273 (by rw [he_v273]; exact empty_args) hinv264 h64 as ⟨v273, s265, hinv265, h_v273⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 dropping he_v273 hinv264 e_v273 s264
  step as ⟨e_v274, he_v274⟩
  store_step with CtorSpec.eo__40purify.construct s265 e_v274 (by rw [he_v274]; exact empty_args) hinv265 h64 as ⟨v274, s266, hinv266, h_v274⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 dropping he_v274 hinv265 e_v274 s265
  step as ⟨e_v275, he_v275⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s266 e_v275 (by rw [he_v275]; exact empty_args) hinv266 h64 as ⟨v275, s267, hinv267, h_v275⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 dropping he_v275 hinv266 e_v275 s266
  step as ⟨e_v276, he_v276⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s267 e_v276 (by rw [he_v276]; exact empty_args) hinv267 h64 as ⟨v276, s268, hinv268, h_v276⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 dropping he_v276 hinv267 e_v276 s267
  store_step with Store.apply_rep s268 v276 v8 _ _ hinv268 h64 h_v276 h_v8 (by ns_tac) (by ns_tac) as ⟨v277, s269, hinv269, h_v277⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 dropping h_v276 hinv268 s268 v276
  store_step with Store.apply_rep s269 v277 v2 _ _ hinv269 h64 h_v277 h_v2 (by ns_tac) (by ns_tac) as ⟨v278, s270, hinv270, h_v278⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 dropping h_v277 hinv269 s269 v277
  step as ⟨e_v279, he_v279⟩
  store_step with CtorSpec.eo__2d.construct s270 e_v279 (by rw [he_v279]; exact empty_args) hinv270 h64 as ⟨v279, s271, hinv271, h_v279⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 h_v278 dropping he_v279 hinv270 e_v279 s270
  step as ⟨e_v280, he_v280⟩
  store_step with CtorSpec.eo_str_2elen.construct s271 e_v280 (by rw [he_v280]; exact empty_args) hinv271 h64 as ⟨v280, s272, hinv272, h_v280⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 h_v278 h_v279 dropping he_v280 hinv271 e_v280 s271
  store_step with Store.apply_rep s272 v280 v8 _ _ hinv272 h64 h_v280 h_v8 (by ns_tac) (by ns_tac) as ⟨v281, s273, hinv273, h_v281⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 h_v278 h_v279 dropping h_v280 hinv272 s272 v280
  store_step with Store.apply_rep s273 v279 v281 _ _ hinv273 h64 h_v279 h_v281 (by ns_tac) (by ns_tac) as ⟨v282, s274, hinv274, h_v282⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 h_v278 dropping h_v279 h_v281 hinv273 s273 v279 v281
  store_step with Store.apply_rep s274 v282 v2 _ _ hinv274 h64 h_v282 h_v2 (by ns_tac) (by ns_tac) as ⟨v283, s275, hinv275, h_v283⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 h_v278 dropping h_v282 hinv274 s274 v282
  store_step with Store.apply_rep s275 v278 v283 _ _ hinv275 h64 h_v278 h_v283 (by ns_tac) (by ns_tac) as ⟨v284, s276, hinv276, h_v284⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v275 dropping h_v278 h_v283 hinv275 s275 v278 v283
  store_step with Store.apply_rep s276 v275 v284 _ _ hinv276 h64 h_v275 h_v284 (by ns_tac) (by ns_tac) as ⟨v285, s277, hinv277, h_v285⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 dropping h_v275 h_v284 hinv276 s276 v275 v284
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s277 0#u32 (0) (by scalar_tac) hinv277 h64 as ⟨v286, s278, hinv278, h_v286⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v285 dropping hinv277 s277
  store_step with Store.apply_rep s278 v285 v286 _ _ hinv278 h64 h_v285 h_v286 (by ns_tac) (by ns_tac) as ⟨v287, s279, hinv279, h_v287⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 dropping h_v285 h_v286 hinv278 s278 v285 v286
  step as ⟨e_v288, he_v288⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s279 e_v288 (by rw [he_v288]; exact empty_args) hinv279 h64 as ⟨v288, s280, hinv280, h_v288⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 dropping he_v288 hinv279 e_v288 s279
  step as ⟨e_v289, he_v289⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s280 e_v289 (by rw [he_v289]; exact empty_args) hinv280 h64 as ⟨v289, s281, hinv281, h_v289⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 dropping he_v289 hinv280 e_v289 s280
  store_step with Store.apply_rep s281 v289 v8 _ _ hinv281 h64 h_v289 h_v8 (by ns_tac) (by ns_tac) as ⟨v290, s282, hinv282, h_v290⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 dropping h_v289 hinv281 s281 v289
  store_step with Store.apply_rep s282 v290 v2 _ _ hinv282 h64 h_v290 h_v2 (by ns_tac) (by ns_tac) as ⟨v291, s283, hinv283, h_v291⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 dropping h_v290 hinv282 s282 v290
  step as ⟨e_v292, he_v292⟩
  store_step with CtorSpec.eo__2d.construct s283 e_v292 (by rw [he_v292]; exact empty_args) hinv283 h64 as ⟨v292, s284, hinv284, h_v292⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 h_v291 dropping he_v292 hinv283 e_v292 s283
  step as ⟨e_v293, he_v293⟩
  store_step with CtorSpec.eo_str_2elen.construct s284 e_v293 (by rw [he_v293]; exact empty_args) hinv284 h64 as ⟨v293, s285, hinv285, h_v293⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 h_v291 h_v292 dropping he_v293 hinv284 e_v293 s284
  store_step with Store.apply_rep s285 v293 v8 _ _ hinv285 h64 h_v293 h_v8 (by ns_tac) (by ns_tac) as ⟨v294, s286, hinv286, h_v294⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 h_v291 h_v292 dropping h_v293 hinv285 s285 v293
  store_step with Store.apply_rep s286 v292 v294 _ _ hinv286 h64 h_v292 h_v294 (by ns_tac) (by ns_tac) as ⟨v295, s287, hinv287, h_v295⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 h_v291 dropping h_v292 h_v294 hinv286 s286 v292 v294
  store_step with Store.apply_rep s287 v295 v2 _ _ hinv287 h64 h_v295 h_v2 (by ns_tac) (by ns_tac) as ⟨v296, s288, hinv288, h_v296⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 h_v291 dropping h_v295 hinv287 s287 v295
  store_step with Store.apply_rep s288 v291 v296 _ _ hinv288 h64 h_v291 h_v296 (by ns_tac) (by ns_tac) as ⟨v297, s289, hinv289, h_v297⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v288 dropping h_v291 h_v296 hinv288 s288 v291 v296
  store_step with Store.apply_rep s289 v288 v297 _ _ hinv289 h64 h_v288 h_v297 (by ns_tac) (by ns_tac) as ⟨v298, s290, hinv290, h_v298⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 dropping h_v288 h_v297 hinv289 s289 v288 v297
  store_step with Store.apply_rep s290 v298 v5 _ _ hinv290 h64 h_v298 h_v5 (by ns_tac) (by ns_tac) as ⟨v299, s291, hinv291, h_v299⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 dropping h_v298 hinv290 s290 v298
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s291 0#u32 (0) (by scalar_tac) hinv291 h64 as ⟨v300, s292, hinv292, h_v300⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 h_v299 dropping hinv291 s291
  store_step with Store.apply_rep s292 v299 v300 _ _ hinv292 h64 h_v299 h_v300 (by ns_tac) (by ns_tac) as ⟨v301, s293, hinv293, h_v301⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 h_v287 dropping h_v299 h_v300 hinv292 s292 v299 v300
  store_step with Store.apply_rep s293 v287 v301 _ _ hinv293 h64 h_v287 h_v301 (by ns_tac) (by ns_tac) as ⟨v302, s294, hinv294, h_v302⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 h_v274 dropping h_v287 h_v301 hinv293 s293 v287 v301
  store_step with Store.apply_rep s294 v274 v302 _ _ hinv294 h64 h_v274 h_v302 (by ns_tac) (by ns_tac) as ⟨v303, s295, hinv295, h_v303⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v273 dropping h_v274 h_v302 hinv294 s294 v274 v302
  store_step with Store.apply_rep s295 v273 v303 _ _ hinv295 h64 h_v273 h_v303 (by ns_tac) (by ns_tac) as ⟨v304, s296, hinv296, h_v304⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 dropping h_v273 h_v303 hinv295 s295 v273 v303
  step as ⟨e_v305, he_v305⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s296 e_v305 (by rw [he_v305]; exact empty_args) hinv296 h64 as ⟨v305, s297, hinv297, h_v305⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 dropping he_v305 hinv296 e_v305 s296
  step as ⟨e_v306, he_v306⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s297 e_v306 (by rw [he_v306]; exact empty_args) hinv297 h64 as ⟨v306, s298, hinv298, h_v306⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 dropping he_v306 hinv297 e_v306 s297
  store_step with Store.apply_rep s298 v306 v5 _ _ hinv298 h64 h_v306 h_v5 (by ns_tac) (by ns_tac) as ⟨v307, s299, hinv299, h_v307⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 dropping h_v306 hinv298 s298 v306
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s299 0#u32 (0) (by scalar_tac) hinv299 h64 as ⟨v308, s300, hinv300, h_v308⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v307 dropping hinv299 s299
  store_step with Store.apply_rep s300 v307 v308 _ _ hinv300 h64 h_v307 h_v308 (by ns_tac) (by ns_tac) as ⟨v309, s301, hinv301, h_v309⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 dropping h_v307 h_v308 hinv300 s300 v307 v308
  step as ⟨e_v310, he_v310⟩
  store_step with CtorSpec.eo__2d.construct s301 e_v310 (by rw [he_v310]; exact empty_args) hinv301 h64 as ⟨v310, s302, hinv302, h_v310⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v309 dropping he_v310 hinv301 e_v310 s301
  step as ⟨e_v311, he_v311⟩
  store_step with CtorSpec.eo_str_2elen.construct s302 e_v311 (by rw [he_v311]; exact empty_args) hinv302 h64 as ⟨v311, s303, hinv303, h_v311⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v309 h_v310 dropping he_v311 hinv302 e_v311 s302
  store_step with Store.apply_rep s303 v311 v5 _ _ hinv303 h64 h_v311 h_v5 (by ns_tac) (by ns_tac) as ⟨v312, s304, hinv304, h_v312⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v309 h_v310 dropping h_v311 hinv303 s303 v311
  store_step with Store.apply_rep s304 v310 v312 _ _ hinv304 h64 h_v310 h_v312 (by ns_tac) (by ns_tac) as ⟨v313, s305, hinv305, h_v313⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v309 dropping h_v310 h_v312 hinv304 s304 v310 v312
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s305 1#u32 (1) (by scalar_tac) hinv305 h64 as ⟨v314, s306, hinv306, h_v314⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v309 h_v313 dropping hinv305 s305
  store_step with Store.apply_rep s306 v313 v314 _ _ hinv306 h64 h_v313 h_v314 (by ns_tac) (by ns_tac) as ⟨v315, s307, hinv307, h_v315⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 h_v309 dropping h_v313 h_v314 hinv306 s306 v313 v314
  store_step with Store.apply_rep s307 v309 v315 _ _ hinv307 h64 h_v309 h_v315 (by ns_tac) (by ns_tac) as ⟨v316, s308, hinv308, h_v316⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v305 dropping h_v309 h_v315 hinv307 s307 v309 v315
  store_step with Store.apply_rep s308 v305 v316 _ _ hinv308 h64 h_v305 h_v316 (by ns_tac) (by ns_tac) as ⟨v317, s309, hinv309, h_v317⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 dropping h_v305 h_v316 hinv308 s308 v305 v316
  step as ⟨e_v318, he_v318⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s309 e_v318 (by rw [he_v318]; exact empty_args) hinv309 h64 as ⟨v318, s310, hinv310, h_v318⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 dropping he_v318 hinv309 e_v318 s309
  step as ⟨e_v319, he_v319⟩
  store_step with CtorSpec.eo__40purify.construct s310 e_v319 (by rw [he_v319]; exact empty_args) hinv310 h64 as ⟨v319, s311, hinv311, h_v319⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 dropping he_v319 hinv310 e_v319 s310
  step as ⟨e_v320, he_v320⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s311 e_v320 (by rw [he_v320]; exact empty_args) hinv311 h64 as ⟨v320, s312, hinv312, h_v320⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 dropping he_v320 hinv311 e_v320 s311
  step as ⟨e_v321, he_v321⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s312 e_v321 (by rw [he_v321]; exact empty_args) hinv312 h64 as ⟨v321, s313, hinv313, h_v321⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 dropping he_v321 hinv312 e_v321 s312
  store_step with Store.apply_rep s313 v321 v8 _ _ hinv313 h64 h_v321 h_v8 (by ns_tac) (by ns_tac) as ⟨v322, s314, hinv314, h_v322⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 dropping h_v321 hinv313 s313 v321
  store_step with Store.apply_rep s314 v322 v2 _ _ hinv314 h64 h_v322 h_v2 (by ns_tac) (by ns_tac) as ⟨v323, s315, hinv315, h_v323⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 dropping h_v322 hinv314 s314 v322
  step as ⟨e_v324, he_v324⟩
  store_step with CtorSpec.eo__2d.construct s315 e_v324 (by rw [he_v324]; exact empty_args) hinv315 h64 as ⟨v324, s316, hinv316, h_v324⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 h_v323 dropping he_v324 hinv315 e_v324 s315
  step as ⟨e_v325, he_v325⟩
  store_step with CtorSpec.eo_str_2elen.construct s316 e_v325 (by rw [he_v325]; exact empty_args) hinv316 h64 as ⟨v325, s317, hinv317, h_v325⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 h_v323 h_v324 dropping he_v325 hinv316 e_v325 s316
  store_step with Store.apply_rep s317 v325 v8 _ _ hinv317 h64 h_v325 h_v8 (by ns_tac) (by ns_tac) as ⟨v326, s318, hinv318, h_v326⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 h_v323 h_v324 dropping h_v325 hinv317 s317 v325
  store_step with Store.apply_rep s318 v324 v326 _ _ hinv318 h64 h_v324 h_v326 (by ns_tac) (by ns_tac) as ⟨v327, s319, hinv319, h_v327⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 h_v323 dropping h_v324 h_v326 hinv318 s318 v324 v326
  store_step with Store.apply_rep s319 v327 v2 _ _ hinv319 h64 h_v327 h_v2 (by ns_tac) (by ns_tac) as ⟨v328, s320, hinv320, h_v328⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 h_v323 dropping h_v327 hinv319 s319 v327
  store_step with Store.apply_rep s320 v323 v328 _ _ hinv320 h64 h_v323 h_v328 (by ns_tac) (by ns_tac) as ⟨v329, s321, hinv321, h_v329⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v320 dropping h_v323 h_v328 hinv320 s320 v323 v328
  store_step with Store.apply_rep s321 v320 v329 _ _ hinv321 h64 h_v320 h_v329 (by ns_tac) (by ns_tac) as ⟨v330, s322, hinv322, h_v330⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 dropping h_v320 h_v329 hinv321 s321 v320 v329
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s322 0#u32 (0) (by scalar_tac) hinv322 h64 as ⟨v331, s323, hinv323, h_v331⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v330 dropping hinv322 s322
  store_step with Store.apply_rep s323 v330 v331 _ _ hinv323 h64 h_v330 h_v331 (by ns_tac) (by ns_tac) as ⟨v332, s324, hinv324, h_v332⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 dropping h_v330 h_v331 hinv323 s323 v330 v331
  step as ⟨e_v333, he_v333⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s324 e_v333 (by rw [he_v333]; exact empty_args) hinv324 h64 as ⟨v333, s325, hinv325, h_v333⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 dropping he_v333 hinv324 e_v333 s324
  step as ⟨e_v334, he_v334⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s325 e_v334 (by rw [he_v334]; exact empty_args) hinv325 h64 as ⟨v334, s326, hinv326, h_v334⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 dropping he_v334 hinv325 e_v334 s325
  store_step with Store.apply_rep s326 v334 v8 _ _ hinv326 h64 h_v334 h_v8 (by ns_tac) (by ns_tac) as ⟨v335, s327, hinv327, h_v335⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 dropping h_v334 hinv326 s326 v334
  store_step with Store.apply_rep s327 v335 v2 _ _ hinv327 h64 h_v335 h_v2 (by ns_tac) (by ns_tac) as ⟨v336, s328, hinv328, h_v336⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 dropping h_v335 hinv327 s327 v335
  step as ⟨e_v337, he_v337⟩
  store_step with CtorSpec.eo__2d.construct s328 e_v337 (by rw [he_v337]; exact empty_args) hinv328 h64 as ⟨v337, s329, hinv329, h_v337⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 h_v336 dropping he_v337 hinv328 e_v337 s328
  step as ⟨e_v338, he_v338⟩
  store_step with CtorSpec.eo_str_2elen.construct s329 e_v338 (by rw [he_v338]; exact empty_args) hinv329 h64 as ⟨v338, s330, hinv330, h_v338⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 h_v336 h_v337 dropping he_v338 hinv329 e_v338 s329
  store_step with Store.apply_rep s330 v338 v8 _ _ hinv330 h64 h_v338 h_v8 (by ns_tac) (by ns_tac) as ⟨v339, s331, hinv331, h_v339⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 h_v336 h_v337 dropping h_v338 hinv330 s330 v338
  store_step with Store.apply_rep s331 v337 v339 _ _ hinv331 h64 h_v337 h_v339 (by ns_tac) (by ns_tac) as ⟨v340, s332, hinv332, h_v340⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 h_v336 dropping h_v337 h_v339 hinv331 s331 v337 v339
  store_step with Store.apply_rep s332 v340 v2 _ _ hinv332 h64 h_v340 h_v2 (by ns_tac) (by ns_tac) as ⟨v341, s333, hinv333, h_v341⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 h_v336 dropping h_v340 hinv332 s332 v340
  store_step with Store.apply_rep s333 v336 v341 _ _ hinv333 h64 h_v336 h_v341 (by ns_tac) (by ns_tac) as ⟨v342, s334, hinv334, h_v342⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v333 dropping h_v336 h_v341 hinv333 s333 v336 v341
  store_step with Store.apply_rep s334 v333 v342 _ _ hinv334 h64 h_v333 h_v342 (by ns_tac) (by ns_tac) as ⟨v343, s335, hinv335, h_v343⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 dropping h_v333 h_v342 hinv334 s334 v333 v342
  store_step with Store.apply_rep s335 v343 v5 _ _ hinv335 h64 h_v343 h_v5 (by ns_tac) (by ns_tac) as ⟨v344, s336, hinv336, h_v344⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 dropping h_v343 hinv335 s335 v343
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s336 0#u32 (0) (by scalar_tac) hinv336 h64 as ⟨v345, s337, hinv337, h_v345⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 h_v344 dropping hinv336 s336
  store_step with Store.apply_rep s337 v344 v345 _ _ hinv337 h64 h_v344 h_v345 (by ns_tac) (by ns_tac) as ⟨v346, s338, hinv338, h_v346⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 h_v332 dropping h_v344 h_v345 hinv337 s337 v344 v345
  store_step with Store.apply_rep s338 v332 v346 _ _ hinv338 h64 h_v332 h_v346 (by ns_tac) (by ns_tac) as ⟨v347, s339, hinv339, h_v347⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 h_v319 dropping h_v332 h_v346 hinv338 s338 v332 v346
  store_step with Store.apply_rep s339 v319 v347 _ _ hinv339 h64 h_v319 h_v347 (by ns_tac) (by ns_tac) as ⟨v348, s340, hinv340, h_v348⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 dropping h_v319 h_v347 hinv339 s339 v319 v347
  store_step with ih.eo__24eo_5ftypeof s340 v348 _ hinv340 h64 (hG.rem hrem) h_v348 as ⟨v349, s341, hinv341, h_v349⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 h_v318 dropping h_v348 hinv340 s340 v348
  store_step with ih.eo__24eo_5fnil s341 v318 v349 _ _ hinv341 h64 (hG.rem hrem) h_v318 h_v349 as ⟨v350, s342, hinv342, h_v350⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 h_v317 dropping h_v318 h_v349 hinv341 s341 v318 v349
  store_step with Store.apply_mk_rep s342 v317 v350 _ _ hinv342 h64 h_v317 h_v350 as ⟨v351, s343, hinv343, h_v351⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 h_v304 dropping h_v317 h_v350 hinv342 s342 v317 v350
  store_step with Store.apply_mk_rep s343 v304 v351 _ _ hinv343 h64 h_v304 h_v351 as ⟨v352, s344, hinv344, h_v352⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 h_v272 dropping h_v304 h_v351 hinv343 s343 v304 v351
  store_step with Store.apply_mk_rep s344 v272 v352 _ _ hinv344 h64 h_v272 h_v352 as ⟨v353, s345, hinv345, h_v353⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 dropping h_v272 h_v352 hinv344 s344 v272 v352
  store_step with Store.apply_mk_rep s345 v353 v5 _ _ hinv345 h64 h_v353 h_v5 as ⟨v354, s346, hinv346, h_v354⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 h_v271 dropping h_v353 hinv345 s345 v353
  store_step with Store.apply_mk_rep s346 v271 v354 _ _ hinv346 h64 h_v271 h_v354 as ⟨v355, s347, hinv347, h_v355⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v270 dropping h_v271 h_v354 hinv346 s346 v271 v354
  store_step with Store.apply_mk_rep s347 v270 v355 _ _ hinv347 h64 h_v270 h_v355 as ⟨v356, s348, hinv348, h_v356⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 dropping h_v270 h_v355 hinv347 s347 v270 v355
  step as ⟨e_v357, he_v357⟩
  store_step with CtorSpec.eo_and.construct s348 e_v357 (by rw [he_v357]; exact empty_args) hinv348 h64 as ⟨v357, s349, hinv349, h_v357⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 dropping he_v357 hinv348 e_v357 s348
  step as ⟨e_v358, he_v358⟩
  store_step with CtorSpec.eo__3d.construct s349 e_v358 (by rw [he_v358]; exact empty_args) hinv349 h64 as ⟨v358, s350, hinv350, h_v358⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 dropping he_v358 hinv349 e_v358 s349
  step as ⟨e_v359, he_v359⟩
  store_step with CtorSpec.eo__40purify.construct s350 e_v359 (by rw [he_v359]; exact empty_args) hinv350 h64 as ⟨v359, s351, hinv351, h_v359⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v358 dropping he_v359 hinv350 e_v359 s350
  step as ⟨e_v360, he_v360⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s351 e_v360 (by rw [he_v360]; exact empty_args) hinv351 h64 as ⟨v360, s352, hinv352, h_v360⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v358 h_v359 dropping he_v360 hinv351 e_v360 s351
  store_step with Store.apply_rep s352 v360 v8 _ _ hinv352 h64 h_v360 h_v8 (by ns_tac) (by ns_tac) as ⟨v361, s353, hinv353, h_v361⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v358 h_v359 dropping h_v360 hinv352 s352 v360
  store_step with Store.apply_rep s353 v361 v5 _ _ hinv353 h64 h_v361 h_v5 (by ns_tac) (by ns_tac) as ⟨v362, s354, hinv354, h_v362⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v358 h_v359 dropping h_v361 hinv353 s353 v361
  store_step with Store.apply_rep s354 v362 v2 _ _ hinv354 h64 h_v362 h_v2 (by ns_tac) (by ns_tac) as ⟨v363, s355, hinv355, h_v363⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v358 h_v359 dropping h_v362 hinv354 s354 v362
  store_step with Store.apply_rep s355 v359 v363 _ _ hinv355 h64 h_v359 h_v363 (by ns_tac) (by ns_tac) as ⟨v364, s356, hinv356, h_v364⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v358 dropping h_v359 h_v363 hinv355 s355 v359 v363
  store_step with Store.apply_rep s356 v358 v364 _ _ hinv356 h64 h_v358 h_v364 (by ns_tac) (by ns_tac) as ⟨v365, s357, hinv357, h_v365⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 dropping h_v358 h_v364 hinv356 s356 v358 v364
  step as ⟨e_v366, he_v366⟩
  store_step with CtorSpec.eo__2b.construct s357 e_v366 (by rw [he_v366]; exact empty_args) hinv357 h64 as ⟨v366, s358, hinv358, h_v366⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 dropping he_v366 hinv357 e_v366 s357
  store_step with Store.apply_rep s358 v366 v2 _ _ hinv358 h64 h_v366 h_v2 (by ns_tac) (by ns_tac) as ⟨v367, s359, hinv359, h_v367⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 dropping h_v366 hinv358 s358 v366
  step as ⟨e_v368, he_v368⟩
  store_step with CtorSpec.eo__2b.construct s359 e_v368 (by rw [he_v368]; exact empty_args) hinv359 h64 as ⟨v368, s360, hinv360, h_v368⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 dropping he_v368 hinv359 e_v368 s359
  step as ⟨e_v369, he_v369⟩
  store_step with CtorSpec.eo_str_2elen.construct s360 e_v369 (by rw [he_v369]; exact empty_args) hinv360 h64 as ⟨v369, s361, hinv361, h_v369⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 dropping he_v369 hinv360 e_v369 s360
  step as ⟨e_v370, he_v370⟩
  store_step with CtorSpec.eo__40purify.construct s361 e_v370 (by rw [he_v370]; exact empty_args) hinv361 h64 as ⟨v370, s362, hinv362, h_v370⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 dropping he_v370 hinv361 e_v370 s361
  step as ⟨e_v371, he_v371⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s362 e_v371 (by rw [he_v371]; exact empty_args) hinv362 h64 as ⟨v371, s363, hinv363, h_v371⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 dropping he_v371 hinv362 e_v371 s362
  step as ⟨e_v372, he_v372⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s363 e_v372 (by rw [he_v372]; exact empty_args) hinv363 h64 as ⟨v372, s364, hinv364, h_v372⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 dropping he_v372 hinv363 e_v372 s363
  store_step with Store.apply_rep s364 v372 v8 _ _ hinv364 h64 h_v372 h_v8 (by ns_tac) (by ns_tac) as ⟨v373, s365, hinv365, h_v373⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 dropping h_v372 hinv364 s364 v372
  store_step with Store.apply_rep s365 v373 v2 _ _ hinv365 h64 h_v373 h_v2 (by ns_tac) (by ns_tac) as ⟨v374, s366, hinv366, h_v374⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 dropping h_v373 hinv365 s365 v373
  step as ⟨e_v375, he_v375⟩
  store_step with CtorSpec.eo__2d.construct s366 e_v375 (by rw [he_v375]; exact empty_args) hinv366 h64 as ⟨v375, s367, hinv367, h_v375⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 h_v374 dropping he_v375 hinv366 e_v375 s366
  step as ⟨e_v376, he_v376⟩
  store_step with CtorSpec.eo_str_2elen.construct s367 e_v376 (by rw [he_v376]; exact empty_args) hinv367 h64 as ⟨v376, s368, hinv368, h_v376⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 h_v374 h_v375 dropping he_v376 hinv367 e_v376 s367
  store_step with Store.apply_rep s368 v376 v8 _ _ hinv368 h64 h_v376 h_v8 (by ns_tac) (by ns_tac) as ⟨v377, s369, hinv369, h_v377⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 h_v374 h_v375 dropping h_v376 hinv368 s368 v376
  store_step with Store.apply_rep s369 v375 v377 _ _ hinv369 h64 h_v375 h_v377 (by ns_tac) (by ns_tac) as ⟨v378, s370, hinv370, h_v378⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 h_v374 dropping h_v375 h_v377 hinv369 s369 v375 v377
  store_step with Store.apply_rep s370 v378 v2 _ _ hinv370 h64 h_v378 h_v2 (by ns_tac) (by ns_tac) as ⟨v379, s371, hinv371, h_v379⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 h_v374 dropping h_v378 hinv370 s370 v378
  store_step with Store.apply_rep s371 v374 v379 _ _ hinv371 h64 h_v374 h_v379 (by ns_tac) (by ns_tac) as ⟨v380, s372, hinv372, h_v380⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v371 dropping h_v374 h_v379 hinv371 s371 v374 v379
  store_step with Store.apply_rep s372 v371 v380 _ _ hinv372 h64 h_v371 h_v380 (by ns_tac) (by ns_tac) as ⟨v381, s373, hinv373, h_v381⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 dropping h_v371 h_v380 hinv372 s372 v371 v380
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s373 0#u32 (0) (by scalar_tac) hinv373 h64 as ⟨v382, s374, hinv374, h_v382⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v381 dropping hinv373 s373
  store_step with Store.apply_rep s374 v381 v382 _ _ hinv374 h64 h_v381 h_v382 (by ns_tac) (by ns_tac) as ⟨v383, s375, hinv375, h_v383⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 dropping h_v381 h_v382 hinv374 s374 v381 v382
  step as ⟨e_v384, he_v384⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s375 e_v384 (by rw [he_v384]; exact empty_args) hinv375 h64 as ⟨v384, s376, hinv376, h_v384⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 dropping he_v384 hinv375 e_v384 s375
  step as ⟨e_v385, he_v385⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s376 e_v385 (by rw [he_v385]; exact empty_args) hinv376 h64 as ⟨v385, s377, hinv377, h_v385⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 dropping he_v385 hinv376 e_v385 s376
  store_step with Store.apply_rep s377 v385 v8 _ _ hinv377 h64 h_v385 h_v8 (by ns_tac) (by ns_tac) as ⟨v386, s378, hinv378, h_v386⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 dropping h_v385 hinv377 s377 v385
  store_step with Store.apply_rep s378 v386 v2 _ _ hinv378 h64 h_v386 h_v2 (by ns_tac) (by ns_tac) as ⟨v387, s379, hinv379, h_v387⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 dropping h_v386 hinv378 s378 v386
  step as ⟨e_v388, he_v388⟩
  store_step with CtorSpec.eo__2d.construct s379 e_v388 (by rw [he_v388]; exact empty_args) hinv379 h64 as ⟨v388, s380, hinv380, h_v388⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 h_v387 dropping he_v388 hinv379 e_v388 s379
  step as ⟨e_v389, he_v389⟩
  store_step with CtorSpec.eo_str_2elen.construct s380 e_v389 (by rw [he_v389]; exact empty_args) hinv380 h64 as ⟨v389, s381, hinv381, h_v389⟩ growing hG carrying h_v2 h_v5 h_v8 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 h_v387 h_v388 dropping he_v389 hinv380 e_v389 s380
  store_step with Store.apply_rep s381 v389 v8 _ _ hinv381 h64 h_v389 h_v8 (by ns_tac) (by ns_tac) as ⟨v390, s382, hinv382, h_v390⟩ growing hG carrying h_v2 h_v5 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 h_v387 h_v388 dropping h_v389 h_v8 hinv381 s381 v389 v8
  store_step with Store.apply_rep s382 v388 v390 _ _ hinv382 h64 h_v388 h_v390 (by ns_tac) (by ns_tac) as ⟨v391, s383, hinv383, h_v391⟩ growing hG carrying h_v2 h_v5 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 h_v387 dropping h_v388 h_v390 hinv382 s382 v388 v390
  store_step with Store.apply_rep s383 v391 v2 _ _ hinv383 h64 h_v391 h_v2 (by ns_tac) (by ns_tac) as ⟨v392, s384, hinv384, h_v392⟩ growing hG carrying h_v5 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 h_v387 dropping h_v2 h_v391 hinv383 s383 v2 v391
  store_step with Store.apply_rep s384 v387 v392 _ _ hinv384 h64 h_v387 h_v392 (by ns_tac) (by ns_tac) as ⟨v393, s385, hinv385, h_v393⟩ growing hG carrying h_v5 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v384 dropping h_v387 h_v392 hinv384 s384 v387 v392
  store_step with Store.apply_rep s385 v384 v393 _ _ hinv385 h64 h_v384 h_v393 (by ns_tac) (by ns_tac) as ⟨v394, s386, hinv386, h_v394⟩ growing hG carrying h_v5 h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 dropping h_v384 h_v393 hinv385 s385 v384 v393
  store_step with Store.apply_rep s386 v394 v5 _ _ hinv386 h64 h_v394 h_v5 (by ns_tac) (by ns_tac) as ⟨v395, s387, hinv387, h_v395⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 dropping h_v394 h_v5 hinv386 s386 v394 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s387 0#u32 (0) (by scalar_tac) hinv387 h64 as ⟨v396, s388, hinv388, h_v396⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 h_v395 dropping hinv387 s387
  store_step with Store.apply_rep s388 v395 v396 _ _ hinv388 h64 h_v395 h_v396 (by ns_tac) (by ns_tac) as ⟨v397, s389, hinv389, h_v397⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 h_v383 dropping h_v395 h_v396 hinv388 s388 v395 v396
  store_step with Store.apply_rep s389 v383 v397 _ _ hinv389 h64 h_v383 h_v397 (by ns_tac) (by ns_tac) as ⟨v398, s390, hinv390, h_v398⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 h_v370 dropping h_v383 h_v397 hinv389 s389 v383 v397
  store_step with Store.apply_rep s390 v370 v398 _ _ hinv390 h64 h_v370 h_v398 (by ns_tac) (by ns_tac) as ⟨v399, s391, hinv391, h_v399⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 h_v369 dropping h_v370 h_v398 hinv390 s390 v370 v398
  store_step with Store.apply_rep s391 v369 v399 _ _ hinv391 h64 h_v369 h_v399 (by ns_tac) (by ns_tac) as ⟨v400, s392, hinv392, h_v400⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v368 dropping h_v369 h_v399 hinv391 s391 v369 v399
  store_step with Store.apply_rep s392 v368 v400 _ _ hinv392 h64 h_v368 h_v400 (by ns_tac) (by ns_tac) as ⟨v401, s393, hinv393, h_v401⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 dropping h_v368 h_v400 hinv392 s392 v368 v400
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s393 0#u32 (0) (by scalar_tac) hinv393 h64 as ⟨v402, s394, hinv394, h_v402⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 h_v401 dropping hinv393 s393
  store_step with Store.apply_rep s394 v401 v402 _ _ hinv394 h64 h_v401 h_v402 (by ns_tac) (by ns_tac) as ⟨v403, s395, hinv395, h_v403⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 h_v367 dropping h_v401 h_v402 hinv394 s394 v401 v402
  store_step with Store.apply_rep s395 v367 v403 _ _ hinv395 h64 h_v367 h_v403 (by ns_tac) (by ns_tac) as ⟨v404, s396, hinv396, h_v404⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 h_v365 dropping h_v367 h_v403 hinv395 s395 v367 v403
  store_step with Store.apply_rep s396 v365 v404 _ _ hinv396 h64 h_v365 h_v404 (by ns_tac) (by ns_tac) as ⟨v405, s397, hinv397, h_v405⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v357 dropping h_v365 h_v404 hinv396 s396 v365 v404
  store_step with Store.apply_rep s397 v357 v405 _ _ hinv397 h64 h_v357 h_v405 (by ns_tac) (by ns_tac) as ⟨v406, s398, hinv398, h_v406⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 dropping h_v357 h_v405 hinv397 s397 v357 v405
  store_step with Store.literal_boolean_spec s398 true hinv398 h64 as ⟨v407, s399, hinv399, h_v407⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 h_v406 dropping hinv398 s398
  store_step with Store.apply_rep s399 v406 v407 _ _ hinv399 h64 h_v406 h_v407 (by ns_tac) (by ns_tac) as ⟨v408, s400, hinv400, h_v408⟩ growing hG carrying h_v55 h_v72 h_v269 h_v356 dropping h_v406 h_v407 hinv399 s399 v406 v407
  store_step with Store.apply_mk_rep s400 v356 v408 _ _ hinv400 h64 h_v356 h_v408 as ⟨v409, s401, hinv401, h_v409⟩ growing hG carrying h_v55 h_v72 h_v269 dropping h_v356 h_v408 hinv400 s400 v356 v408
  store_step with Store.apply_mk_rep s401 v269 v409 _ _ hinv401 h64 h_v269 h_v409 as ⟨v410, s402, hinv402, h_v410⟩ growing hG carrying h_v55 h_v72 dropping h_v269 h_v409 hinv401 s401 v269 v409
  store_step with Store.apply_mk_rep s402 v72 v410 _ _ hinv402 h64 h_v72 h_v410 as ⟨v411, s403, hinv403, h_v411⟩ growing hG carrying h_v55 dropping h_v410 h_v72 hinv402 s402 v410 v72
  store_step with Store.apply_mk_rep s403 v55 v411 _ _ hinv403 h64 h_v55 h_v411 as ⟨v412, s404, hinv404, h_v412⟩ growing hG carrying dropping h_v411 h_v55 hinv403 s403 v411 v55
  case_done hinv404 hG with h_v412 in EoCases.__str_reduction_pred.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

set_option maxHeartbeats 9030000 in
theorem case_3_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_3
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_3
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_3
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_3
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  store_step with Store.apply_rep s3 v11 v5 _ _ hinv3 h64 h_v11 h_v5 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 hinv3 s3 v11
  store_step with ih.eo__24eo_5ftypeof s4 v5 _ hinv4 h64 (hG.rem hrem) h_v5 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v12 dropping hinv4 s4
  store_step with ih.eo__24seq_5fempty s5 v13 _ hinv5 h64 (hG.rem hrem) h_v13 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v12 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_mk_rep s6 v12 v14 _ _ hinv6 h64 h_v12 h_v14 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v12 h_v14 hinv6 s6 v12 v14
  store_step with Store.apply_mk_rep s7 v10 v15 _ _ hinv7 h64 h_v10 h_v15 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v15 hinv7 s7 v10 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 dropping he_v17 hinv8 e_v17 s8
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__40purify.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 dropping he_v18 hinv9 e_v18 s9
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping he_v19 hinv10 e_v19 s10
  store_step with Store.apply_rep s11 v19 v8 _ _ hinv11 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping h_v19 hinv11 s11 v19
  store_step with Store.apply_rep s12 v20 v5 _ _ hinv12 h64 h_v20 h_v5 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping h_v20 hinv12 s12 v20
  store_step with Store.apply_rep s13 v21 v2 _ _ hinv13 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping h_v21 hinv13 s13 v21
  store_step with Store.apply_rep s14 v18 v22 _ _ hinv14 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 dropping h_v18 h_v22 hinv14 s14 v18 v22
  store_step with Store.apply_rep s15 v17 v23 _ _ hinv15 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 dropping h_v17 h_v23 hinv15 s15 v17 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v25 (by rw [he_v25]; exact empty_args) hinv16 h64 as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 dropping he_v25 hinv16 e_v25 s16
  store_step with Store.apply_rep s17 v25 v2 _ _ hinv17 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 dropping h_v25 hinv17 s17 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s18 e_v27 (by rw [he_v27]; exact empty_args) hinv18 h64 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 h_v26 dropping he_v27 hinv18 e_v27 s18
  store_step with Store.apply_rep s19 v27 v8 _ _ hinv19 h64 h_v27 h_v8 (by ns_tac) (by ns_tac) as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 h_v26 dropping h_v27 hinv19 s19 v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s20 e_v29 (by rw [he_v29]; exact empty_args) hinv20 h64 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 h_v26 h_v28 dropping he_v29 hinv20 e_v29 s20
  store_step with ih.eo__24eo_5ftypeof s21 v2 _ hinv21 h64 (hG.rem hrem) h_v2 as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 h_v26 h_v28 h_v29 dropping hinv21 s21
  store_step with ih.eo__24eo_5fnil s22 v29 v30 _ _ hinv22 h64 (hG.rem hrem) h_v29 h_v30 as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 h_v26 h_v28 dropping h_v29 h_v30 hinv22 s22 v29 v30
  store_step with Store.apply_mk_rep s23 v28 v31 _ _ hinv23 h64 h_v28 h_v31 as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 h_v26 dropping h_v28 h_v31 hinv23 s23 v28 v31
  store_step with Store.apply_mk_rep s24 v26 v32 _ _ hinv24 h64 h_v26 h_v32 as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v24 dropping h_v26 h_v32 hinv24 s24 v26 v32
  store_step with Store.apply_mk_rep s25 v24 v33 _ _ hinv25 h64 h_v24 h_v33 as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 dropping h_v24 h_v33 hinv25 s25 v24 v33
  store_step with Store.apply_mk_rep s26 v16 v34 _ _ hinv26 h64 h_v16 h_v34 as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v16 h_v34 hinv26 s26 v16 v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_ite.construct s27 e_v36 (by rw [he_v36]; exact empty_args) hinv27 h64 as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 dropping he_v36 hinv27 e_v36 s27
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2econtains.construct s28 e_v37 (by rw [he_v37]; exact empty_args) hinv28 h64 as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v36 dropping he_v37 hinv28 e_v37 s28
  store_step with Store.apply_rep s29 v37 v8 _ _ hinv29 h64 h_v37 h_v8 (by ns_tac) (by ns_tac) as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v36 dropping h_v37 hinv29 s29 v37
  store_step with Store.apply_rep s30 v38 v5 _ _ hinv30 h64 h_v38 h_v5 (by ns_tac) (by ns_tac) as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v36 dropping h_v38 hinv30 s30 v38
  store_step with Store.apply_rep s31 v36 v39 _ _ hinv31 h64 h_v36 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 dropping h_v36 h_v39 hinv31 s31 v36 v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_and.construct s32 e_v41 (by rw [he_v41]; exact empty_args) hinv32 h64 as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 dropping he_v41 hinv32 e_v41 s32
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s33 e_v42 (by rw [he_v42]; exact empty_args) hinv33 h64 as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 dropping he_v42 hinv33 e_v42 s33
  store_step with Store.apply_rep s34 v42 v8 _ _ hinv34 h64 h_v42 h_v8 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 dropping h_v42 hinv34 s34 v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s35 e_v44 (by rw [he_v44]; exact empty_args) hinv35 h64 as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 dropping he_v44 hinv35 e_v44 s35
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__40purify.construct s36 e_v45 (by rw [he_v45]; exact empty_args) hinv36 h64 as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 dropping he_v45 hinv36 e_v45 s36
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s37 e_v46 (by rw [he_v46]; exact empty_args) hinv37 h64 as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 dropping he_v46 hinv37 e_v46 s37
  store_step with Store.apply_rep s38 v46 v8 _ _ hinv38 h64 h_v46 h_v8 (by ns_tac) (by ns_tac) as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 dropping h_v46 hinv38 s38 v46
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s39 0#u32 (0) (by scalar_tac) hinv39 h64 as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 h_v47 dropping hinv39 s39
  store_step with Store.apply_rep s40 v47 v48 _ _ hinv40 h64 h_v47 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 dropping h_v47 h_v48 hinv40 s40 v47 v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s41 e_v50 (by rw [he_v50]; exact empty_args) hinv41 h64 as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 h_v49 dropping he_v50 hinv41 e_v50 s41
  store_step with Store.apply_rep s42 v50 v8 _ _ hinv42 h64 h_v50 h_v8 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 h_v49 dropping h_v50 hinv42 s42 v50
  store_step with Store.apply_rep s43 v51 v5 _ _ hinv43 h64 h_v51 h_v5 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 h_v49 dropping h_v51 hinv43 s43 v51
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 h_v49 h_v52 dropping hinv44 s44
  store_step with Store.apply_rep s45 v52 v53 _ _ hinv45 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 h_v49 dropping h_v52 h_v53 hinv45 s45 v52 v53
  store_step with Store.apply_rep s46 v49 v54 _ _ hinv46 h64 h_v49 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 h_v45 dropping h_v49 h_v54 hinv46 s46 v49 v54
  store_step with Store.apply_rep s47 v45 v55 _ _ hinv47 h64 h_v45 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v44 dropping h_v45 h_v55 hinv47 s47 v45 v55
  store_step with Store.apply_rep s48 v44 v56 _ _ hinv48 h64 h_v44 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 dropping h_v44 h_v56 hinv48 s48 v44 v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s49 e_v58 (by rw [he_v58]; exact empty_args) hinv49 h64 as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 dropping he_v58 hinv49 e_v58 s49
  store_step with Store.apply_rep s50 v58 v5 _ _ hinv50 h64 h_v58 h_v5 (by ns_tac) (by ns_tac) as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 dropping h_v58 hinv50 s50 v58
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s51 e_v60 (by rw [he_v60]; exact empty_args) hinv51 h64 as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 dropping he_v60 hinv51 e_v60 s51
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__40purify.construct s52 e_v61 (by rw [he_v61]; exact empty_args) hinv52 h64 as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 dropping he_v61 hinv52 e_v61 s52
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s53 e_v62 (by rw [he_v62]; exact empty_args) hinv53 h64 as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 dropping he_v62 hinv53 e_v62 s53
  store_step with Store.apply_rep s54 v62 v8 _ _ hinv54 h64 h_v62 h_v8 (by ns_tac) (by ns_tac) as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 dropping h_v62 hinv54 s54 v62
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo__2b.construct s55 e_v64 (by rw [he_v64]; exact empty_args) hinv55 h64 as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 dropping he_v64 hinv55 e_v64 s55
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_str_2elen.construct s56 e_v65 (by rw [he_v65]; exact empty_args) hinv56 h64 as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 dropping he_v65 hinv56 e_v65 s56
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo__40purify.construct s57 e_v66 (by rw [he_v66]; exact empty_args) hinv57 h64 as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 dropping he_v66 hinv57 e_v66 s57
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s58 e_v67 (by rw [he_v67]; exact empty_args) hinv58 h64 as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 dropping he_v67 hinv58 e_v67 s58
  store_step with Store.apply_rep s59 v67 v8 _ _ hinv59 h64 h_v67 h_v8 (by ns_tac) (by ns_tac) as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 dropping h_v67 hinv59 s59 v67
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s60 0#u32 (0) (by scalar_tac) hinv60 h64 as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 dropping hinv60 s60
  store_step with Store.apply_rep s61 v68 v69 _ _ hinv61 h64 h_v68 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 dropping h_v68 h_v69 hinv61 s61 v68 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s62 e_v71 (by rw [he_v71]; exact empty_args) hinv62 h64 as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v70 dropping he_v71 hinv62 e_v71 s62
  store_step with Store.apply_rep s63 v71 v8 _ _ hinv63 h64 h_v71 h_v8 (by ns_tac) (by ns_tac) as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v70 dropping h_v71 hinv63 s63 v71
  store_step with Store.apply_rep s64 v72 v5 _ _ hinv64 h64 h_v72 h_v5 (by ns_tac) (by ns_tac) as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v70 dropping h_v72 hinv64 s64 v72
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s65 0#u32 (0) (by scalar_tac) hinv65 h64 as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v70 h_v73 dropping hinv65 s65
  store_step with Store.apply_rep s66 v73 v74 _ _ hinv66 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v70 dropping h_v73 h_v74 hinv66 s66 v73 v74
  store_step with Store.apply_rep s67 v70 v75 _ _ hinv67 h64 h_v70 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 dropping h_v70 h_v75 hinv67 s67 v70 v75
  store_step with Store.apply_rep s68 v66 v76 _ _ hinv68 h64 h_v66 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 h_v65 dropping h_v66 h_v76 hinv68 s68 v66 v76
  store_step with Store.apply_rep s69 v65 v77 _ _ hinv69 h64 h_v65 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v64 dropping h_v65 h_v77 hinv69 s69 v65 v77
  store_step with Store.apply_rep s70 v64 v78 _ _ hinv70 h64 h_v64 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 dropping h_v64 h_v78 hinv70 s70 v64 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo__2b.construct s71 e_v80 (by rw [he_v80]; exact empty_args) hinv71 h64 as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v79 dropping he_v80 hinv71 e_v80 s71
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo_str_2elen.construct s72 e_v81 (by rw [he_v81]; exact empty_args) hinv72 h64 as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v79 h_v80 dropping he_v81 hinv72 e_v81 s72
  store_step with Store.apply_rep s73 v81 v5 _ _ hinv73 h64 h_v81 h_v5 (by ns_tac) (by ns_tac) as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v79 h_v80 dropping h_v81 hinv73 s73 v81
  store_step with Store.apply_rep s74 v80 v82 _ _ hinv74 h64 h_v80 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v79 dropping h_v80 h_v82 hinv74 s74 v80 v82
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s75 0#u32 (0) (by scalar_tac) hinv75 h64 as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v79 h_v83 dropping hinv75 s75
  store_step with Store.apply_rep s76 v83 v84 _ _ hinv76 h64 h_v83 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 h_v79 dropping h_v83 h_v84 hinv76 s76 v83 v84
  store_step with Store.apply_rep s77 v79 v85 _ _ hinv77 h64 h_v79 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v63 dropping h_v79 h_v85 hinv77 s77 v79 v85
  store_step with Store.apply_rep s78 v63 v86 _ _ hinv78 h64 h_v63 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 dropping h_v63 h_v86 hinv78 s78 v63 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo__2d.construct s79 e_v88 (by rw [he_v88]; exact empty_args) hinv79 h64 as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 dropping he_v88 hinv79 e_v88 s79
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo_str_2elen.construct s80 e_v89 (by rw [he_v89]; exact empty_args) hinv80 h64 as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v88 dropping he_v89 hinv80 e_v89 s80
  store_step with Store.apply_rep s81 v89 v8 _ _ hinv81 h64 h_v89 h_v8 (by ns_tac) (by ns_tac) as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v88 dropping h_v89 hinv81 s81 v89
  store_step with Store.apply_rep s82 v88 v90 _ _ hinv82 h64 h_v88 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 dropping h_v88 h_v90 hinv82 s82 v88 v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo__2b.construct s83 e_v92 (by rw [he_v92]; exact empty_args) hinv83 h64 as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 dropping he_v92 hinv83 e_v92 s83
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo_str_2elen.construct s84 e_v93 (by rw [he_v93]; exact empty_args) hinv84 h64 as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 dropping he_v93 hinv84 e_v93 s84
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo__40purify.construct s85 e_v94 (by rw [he_v94]; exact empty_args) hinv85 h64 as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 dropping he_v94 hinv85 e_v94 s85
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s86 e_v95 (by rw [he_v95]; exact empty_args) hinv86 h64 as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 dropping he_v95 hinv86 e_v95 s86
  store_step with Store.apply_rep s87 v95 v8 _ _ hinv87 h64 h_v95 h_v8 (by ns_tac) (by ns_tac) as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 dropping h_v95 hinv87 s87 v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s88 0#u32 (0) (by scalar_tac) hinv88 h64 as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 h_v96 dropping hinv88 s88
  store_step with Store.apply_rep s89 v96 v97 _ _ hinv89 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 dropping h_v96 h_v97 hinv89 s89 v96 v97
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s90 e_v99 (by rw [he_v99]; exact empty_args) hinv90 h64 as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 h_v98 dropping he_v99 hinv90 e_v99 s90
  store_step with Store.apply_rep s91 v99 v8 _ _ hinv91 h64 h_v99 h_v8 (by ns_tac) (by ns_tac) as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 h_v98 dropping h_v99 hinv91 s91 v99
  store_step with Store.apply_rep s92 v100 v5 _ _ hinv92 h64 h_v100 h_v5 (by ns_tac) (by ns_tac) as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 h_v98 dropping h_v100 hinv92 s92 v100
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s93 0#u32 (0) (by scalar_tac) hinv93 h64 as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 h_v98 h_v101 dropping hinv93 s93
  store_step with Store.apply_rep s94 v101 v102 _ _ hinv94 h64 h_v101 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 h_v98 dropping h_v101 h_v102 hinv94 s94 v101 v102
  store_step with Store.apply_rep s95 v98 v103 _ _ hinv95 h64 h_v98 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 h_v94 dropping h_v103 h_v98 hinv95 s95 v103 v98
  store_step with Store.apply_rep s96 v94 v104 _ _ hinv96 h64 h_v94 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 h_v93 dropping h_v104 h_v94 hinv96 s96 v104 v94
  store_step with Store.apply_rep s97 v93 v105 _ _ hinv97 h64 h_v93 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v92 dropping h_v105 h_v93 hinv97 s97 v105 v93
  store_step with Store.apply_rep s98 v92 v106 _ _ hinv98 h64 h_v92 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 dropping h_v106 h_v92 hinv98 s98 v106 v92
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo__2b.construct s99 e_v108 (by rw [he_v108]; exact empty_args) hinv99 h64 as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v107 dropping he_v108 hinv99 e_v108 s99
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_str_2elen.construct s100 e_v109 (by rw [he_v109]; exact empty_args) hinv100 h64 as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v107 h_v108 dropping he_v109 hinv100 e_v109 s100
  store_step with Store.apply_rep s101 v109 v5 _ _ hinv101 h64 h_v109 h_v5 (by ns_tac) (by ns_tac) as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v107 h_v108 dropping h_v109 hinv101 s101 v109
  store_step with Store.apply_rep s102 v108 v110 _ _ hinv102 h64 h_v108 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v107 dropping h_v108 h_v110 hinv102 s102 v108 v110
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s103 0#u32 (0) (by scalar_tac) hinv103 h64 as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v107 h_v111 dropping hinv103 s103
  store_step with Store.apply_rep s104 v111 v112 _ _ hinv104 h64 h_v111 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 h_v107 dropping h_v111 h_v112 hinv104 s104 v111 v112
  store_step with Store.apply_rep s105 v107 v113 _ _ hinv105 h64 h_v107 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 h_v91 dropping h_v107 h_v113 hinv105 s105 v107 v113
  store_step with Store.apply_rep s106 v91 v114 _ _ hinv106 h64 h_v91 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 h_v87 dropping h_v114 h_v91 hinv106 s106 v114 v91
  store_step with Store.apply_rep s107 v87 v115 _ _ hinv107 h64 h_v87 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 h_v61 dropping h_v115 h_v87 hinv107 s107 v115 v87
  store_step with Store.apply_rep s108 v61 v116 _ _ hinv108 h64 h_v61 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v60 dropping h_v116 h_v61 hinv108 s108 v116 v61
  store_step with Store.apply_rep s109 v60 v117 _ _ hinv109 h64 h_v60 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 dropping h_v117 h_v60 hinv109 s109 v117 v60
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s110 e_v119 (by rw [he_v119]; exact empty_args) hinv110 h64 as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 dropping he_v119 hinv110 e_v119 s110
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__40purify.construct s111 e_v120 (by rw [he_v120]; exact empty_args) hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 dropping he_v120 hinv111 e_v120 s111
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s112 e_v121 (by rw [he_v121]; exact empty_args) hinv112 h64 as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 dropping he_v121 hinv112 e_v121 s112
  store_step with Store.apply_rep s113 v121 v8 _ _ hinv113 h64 h_v121 h_v8 (by ns_tac) (by ns_tac) as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 dropping h_v121 hinv113 s113 v121
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s114 0#u32 (0) (by scalar_tac) hinv114 h64 as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 h_v122 dropping hinv114 s114
  store_step with Store.apply_rep s115 v122 v123 _ _ hinv115 h64 h_v122 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 dropping h_v122 h_v123 hinv115 s115 v122 v123
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s116 e_v125 (by rw [he_v125]; exact empty_args) hinv116 h64 as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 h_v124 dropping he_v125 hinv116 e_v125 s116
  store_step with Store.apply_rep s117 v125 v8 _ _ hinv117 h64 h_v125 h_v8 (by ns_tac) (by ns_tac) as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 h_v124 dropping h_v125 hinv117 s117 v125
  store_step with Store.apply_rep s118 v126 v5 _ _ hinv118 h64 h_v126 h_v5 (by ns_tac) (by ns_tac) as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 h_v124 dropping h_v126 hinv118 s118 v126
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s119 0#u32 (0) (by scalar_tac) hinv119 h64 as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 h_v124 h_v127 dropping hinv119 s119
  store_step with Store.apply_rep s120 v127 v128 _ _ hinv120 h64 h_v127 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 h_v124 dropping h_v127 h_v128 hinv120 s120 v127 v128
  store_step with Store.apply_rep s121 v124 v129 _ _ hinv121 h64 h_v124 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 h_v120 dropping h_v124 h_v129 hinv121 s121 v124 v129
  store_step with Store.apply_rep s122 v120 v130 _ _ hinv122 h64 h_v120 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 dropping h_v120 h_v130 hinv122 s122 v120 v130
  store_step with ih.eo__24eo_5ftypeof s123 v131 _ hinv123 h64 (hG.rem hrem) h_v131 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 h_v119 dropping h_v131 hinv123 s123 v131
  store_step with ih.eo__24eo_5fnil s124 v119 v132 _ _ hinv124 h64 (hG.rem hrem) h_v119 h_v132 as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 h_v118 dropping h_v119 h_v132 hinv124 s124 v119 v132
  store_step with Store.apply_mk_rep s125 v118 v133 _ _ hinv125 h64 h_v118 h_v133 as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 h_v59 dropping h_v118 h_v133 hinv125 s125 v118 v133
  store_step with Store.apply_mk_rep s126 v59 v134 _ _ hinv126 h64 h_v59 h_v134 as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 h_v57 dropping h_v134 h_v59 hinv126 s126 v134 v59
  store_step with Store.apply_mk_rep s127 v57 v135 _ _ hinv127 h64 h_v57 h_v135 as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 h_v43 dropping h_v135 h_v57 hinv127 s127 v135 v57
  store_step with Store.apply_mk_rep s128 v43 v136 _ _ hinv128 h64 h_v43 h_v136 as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v41 dropping h_v136 h_v43 hinv128 s128 v136 v43
  store_step with Store.apply_mk_rep s129 v41 v137 _ _ hinv129 h64 h_v41 h_v137 as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 dropping h_v137 h_v41 hinv129 s129 v137 v41
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo_and.construct s130 e_v139 (by rw [he_v139]; exact empty_args) hinv130 h64 as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 dropping he_v139 hinv130 e_v139 s130
  step as ⟨e_v140, he_v140⟩
  store_step with CtorSpec.eo__3d.construct s131 e_v140 (by rw [he_v140]; exact empty_args) hinv131 h64 as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 dropping he_v140 hinv131 e_v140 s131
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo__40purify.construct s132 e_v141 (by rw [he_v141]; exact empty_args) hinv132 h64 as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v140 dropping he_v141 hinv132 e_v141 s132
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s133 e_v142 (by rw [he_v142]; exact empty_args) hinv133 h64 as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v140 h_v141 dropping he_v142 hinv133 e_v142 s133
  store_step with Store.apply_rep s134 v142 v8 _ _ hinv134 h64 h_v142 h_v8 (by ns_tac) (by ns_tac) as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v140 h_v141 dropping h_v142 hinv134 s134 v142
  store_step with Store.apply_rep s135 v143 v5 _ _ hinv135 h64 h_v143 h_v5 (by ns_tac) (by ns_tac) as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v140 h_v141 dropping h_v143 hinv135 s135 v143
  store_step with Store.apply_rep s136 v144 v2 _ _ hinv136 h64 h_v144 h_v2 (by ns_tac) (by ns_tac) as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v140 h_v141 dropping h_v144 hinv136 s136 v144
  store_step with Store.apply_rep s137 v141 v145 _ _ hinv137 h64 h_v141 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v140 dropping h_v141 h_v145 hinv137 s137 v141 v145
  store_step with Store.apply_rep s138 v140 v146 _ _ hinv138 h64 h_v140 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 dropping h_v140 h_v146 hinv138 s138 v140 v146
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s139 e_v148 (by rw [he_v148]; exact empty_args) hinv139 h64 as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 dropping he_v148 hinv139 e_v148 s139
  step as ⟨e_v149, he_v149⟩
  store_step with CtorSpec.eo__40purify.construct s140 e_v149 (by rw [he_v149]; exact empty_args) hinv140 h64 as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 dropping he_v149 hinv140 e_v149 s140
  step as ⟨e_v150, he_v150⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s141 e_v150 (by rw [he_v150]; exact empty_args) hinv141 h64 as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 dropping he_v150 hinv141 e_v150 s141
  store_step with Store.apply_rep s142 v150 v8 _ _ hinv142 h64 h_v150 h_v8 (by ns_tac) (by ns_tac) as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 dropping h_v150 hinv142 s142 v150
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s143 0#u32 (0) (by scalar_tac) hinv143 h64 as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 h_v151 dropping hinv143 s143
  store_step with Store.apply_rep s144 v151 v152 _ _ hinv144 h64 h_v151 h_v152 (by ns_tac) (by ns_tac) as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 dropping h_v151 h_v152 hinv144 s144 v151 v152
  step as ⟨e_v154, he_v154⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s145 e_v154 (by rw [he_v154]; exact empty_args) hinv145 h64 as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 h_v153 dropping he_v154 hinv145 e_v154 s145
  store_step with Store.apply_rep s146 v154 v8 _ _ hinv146 h64 h_v154 h_v8 (by ns_tac) (by ns_tac) as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 h_v153 dropping h_v154 hinv146 s146 v154
  store_step with Store.apply_rep s147 v155 v5 _ _ hinv147 h64 h_v155 h_v5 (by ns_tac) (by ns_tac) as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 h_v153 dropping h_v155 hinv147 s147 v155
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s148 0#u32 (0) (by scalar_tac) hinv148 h64 as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 h_v153 h_v156 dropping hinv148 s148
  store_step with Store.apply_rep s149 v156 v157 _ _ hinv149 h64 h_v156 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 h_v153 dropping h_v156 h_v157 hinv149 s149 v156 v157
  store_step with Store.apply_rep s150 v153 v158 _ _ hinv150 h64 h_v153 h_v158 (by ns_tac) (by ns_tac) as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 h_v149 dropping h_v153 h_v158 hinv150 s150 v153 v158
  store_step with Store.apply_rep s151 v149 v159 _ _ hinv151 h64 h_v149 h_v159 (by ns_tac) (by ns_tac) as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v148 dropping h_v149 h_v159 hinv151 s151 v149 v159
  store_step with Store.apply_rep s152 v148 v160 _ _ hinv152 h64 h_v148 h_v160 (by ns_tac) (by ns_tac) as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 dropping h_v148 h_v160 hinv152 s152 v148 v160
  step as ⟨e_v162, he_v162⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s153 e_v162 (by rw [he_v162]; exact empty_args) hinv153 h64 as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 dropping he_v162 hinv153 e_v162 s153
  store_step with Store.apply_rep s154 v162 v2 _ _ hinv154 h64 h_v162 h_v2 (by ns_tac) (by ns_tac) as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 dropping h_v162 hinv154 s154 v162
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s155 e_v164 (by rw [he_v164]; exact empty_args) hinv155 h64 as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 dropping he_v164 hinv155 e_v164 s155
  step as ⟨e_v165, he_v165⟩
  store_step with CtorSpec.eo__40purify.construct s156 e_v165 (by rw [he_v165]; exact empty_args) hinv156 h64 as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 dropping he_v165 hinv156 e_v165 s156
  step as ⟨e_v166, he_v166⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s157 e_v166 (by rw [he_v166]; exact empty_args) hinv157 h64 as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 dropping he_v166 hinv157 e_v166 s157
  store_step with Store.apply_rep s158 v166 v8 _ _ hinv158 h64 h_v166 h_v8 (by ns_tac) (by ns_tac) as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 dropping h_v166 hinv158 s158 v166
  step as ⟨e_v168, he_v168⟩
  store_step with CtorSpec.eo__2b.construct s159 e_v168 (by rw [he_v168]; exact empty_args) hinv159 h64 as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 dropping he_v168 hinv159 e_v168 s159
  step as ⟨e_v169, he_v169⟩
  store_step with CtorSpec.eo_str_2elen.construct s160 e_v169 (by rw [he_v169]; exact empty_args) hinv160 h64 as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 dropping he_v169 hinv160 e_v169 s160
  step as ⟨e_v170, he_v170⟩
  store_step with CtorSpec.eo__40purify.construct s161 e_v170 (by rw [he_v170]; exact empty_args) hinv161 h64 as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 dropping he_v170 hinv161 e_v170 s161
  step as ⟨e_v171, he_v171⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s162 e_v171 (by rw [he_v171]; exact empty_args) hinv162 h64 as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 dropping he_v171 hinv162 e_v171 s162
  store_step with Store.apply_rep s163 v171 v8 _ _ hinv163 h64 h_v171 h_v8 (by ns_tac) (by ns_tac) as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 dropping h_v171 hinv163 s163 v171
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s164 0#u32 (0) (by scalar_tac) hinv164 h64 as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 h_v172 dropping hinv164 s164
  store_step with Store.apply_rep s165 v172 v173 _ _ hinv165 h64 h_v172 h_v173 (by ns_tac) (by ns_tac) as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 dropping h_v172 h_v173 hinv165 s165 v172 v173
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s166 e_v175 (by rw [he_v175]; exact empty_args) hinv166 h64 as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 h_v174 dropping he_v175 hinv166 e_v175 s166
  store_step with Store.apply_rep s167 v175 v8 _ _ hinv167 h64 h_v175 h_v8 (by ns_tac) (by ns_tac) as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 h_v174 dropping h_v175 hinv167 s167 v175
  store_step with Store.apply_rep s168 v176 v5 _ _ hinv168 h64 h_v176 h_v5 (by ns_tac) (by ns_tac) as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 h_v174 dropping h_v176 hinv168 s168 v176
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s169 0#u32 (0) (by scalar_tac) hinv169 h64 as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 h_v174 h_v177 dropping hinv169 s169
  store_step with Store.apply_rep s170 v177 v178 _ _ hinv170 h64 h_v177 h_v178 (by ns_tac) (by ns_tac) as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 h_v174 dropping h_v177 h_v178 hinv170 s170 v177 v178
  store_step with Store.apply_rep s171 v174 v179 _ _ hinv171 h64 h_v174 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 h_v170 dropping h_v174 h_v179 hinv171 s171 v174 v179
  store_step with Store.apply_rep s172 v170 v180 _ _ hinv172 h64 h_v170 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 h_v169 dropping h_v170 h_v180 hinv172 s172 v170 v180
  store_step with Store.apply_rep s173 v169 v181 _ _ hinv173 h64 h_v169 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v168 dropping h_v169 h_v181 hinv173 s173 v169 v181
  store_step with Store.apply_rep s174 v168 v182 _ _ hinv174 h64 h_v168 h_v182 (by ns_tac) (by ns_tac) as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 dropping h_v168 h_v182 hinv174 s174 v168 v182
  step as ⟨e_v184, he_v184⟩
  store_step with CtorSpec.eo__2b.construct s175 e_v184 (by rw [he_v184]; exact empty_args) hinv175 h64 as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v183 dropping he_v184 hinv175 e_v184 s175
  step as ⟨e_v185, he_v185⟩
  store_step with CtorSpec.eo_str_2elen.construct s176 e_v185 (by rw [he_v185]; exact empty_args) hinv176 h64 as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v183 h_v184 dropping he_v185 hinv176 e_v185 s176
  store_step with Store.apply_rep s177 v185 v5 _ _ hinv177 h64 h_v185 h_v5 (by ns_tac) (by ns_tac) as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v183 h_v184 dropping h_v185 hinv177 s177 v185
  store_step with Store.apply_rep s178 v184 v186 _ _ hinv178 h64 h_v184 h_v186 (by ns_tac) (by ns_tac) as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v183 dropping h_v184 h_v186 hinv178 s178 v184 v186
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s179 0#u32 (0) (by scalar_tac) hinv179 h64 as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v183 h_v187 dropping hinv179 s179
  store_step with Store.apply_rep s180 v187 v188 _ _ hinv180 h64 h_v187 h_v188 (by ns_tac) (by ns_tac) as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 h_v183 dropping h_v187 h_v188 hinv180 s180 v187 v188
  store_step with Store.apply_rep s181 v183 v189 _ _ hinv181 h64 h_v183 h_v189 (by ns_tac) (by ns_tac) as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v167 dropping h_v183 h_v189 hinv181 s181 v183 v189
  store_step with Store.apply_rep s182 v167 v190 _ _ hinv182 h64 h_v167 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 dropping h_v167 h_v190 hinv182 s182 v167 v190
  step as ⟨e_v192, he_v192⟩
  store_step with CtorSpec.eo__2d.construct s183 e_v192 (by rw [he_v192]; exact empty_args) hinv183 h64 as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 dropping he_v192 hinv183 e_v192 s183
  step as ⟨e_v193, he_v193⟩
  store_step with CtorSpec.eo_str_2elen.construct s184 e_v193 (by rw [he_v193]; exact empty_args) hinv184 h64 as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v192 dropping he_v193 hinv184 e_v193 s184
  store_step with Store.apply_rep s185 v193 v8 _ _ hinv185 h64 h_v193 h_v8 (by ns_tac) (by ns_tac) as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v192 dropping h_v193 hinv185 s185 v193
  store_step with Store.apply_rep s186 v192 v194 _ _ hinv186 h64 h_v192 h_v194 (by ns_tac) (by ns_tac) as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 dropping h_v192 h_v194 hinv186 s186 v192 v194
  step as ⟨e_v196, he_v196⟩
  store_step with CtorSpec.eo__2b.construct s187 e_v196 (by rw [he_v196]; exact empty_args) hinv187 h64 as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 dropping he_v196 hinv187 e_v196 s187
  step as ⟨e_v197, he_v197⟩
  store_step with CtorSpec.eo_str_2elen.construct s188 e_v197 (by rw [he_v197]; exact empty_args) hinv188 h64 as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 dropping he_v197 hinv188 e_v197 s188
  step as ⟨e_v198, he_v198⟩
  store_step with CtorSpec.eo__40purify.construct s189 e_v198 (by rw [he_v198]; exact empty_args) hinv189 h64 as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 dropping he_v198 hinv189 e_v198 s189
  step as ⟨e_v199, he_v199⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s190 e_v199 (by rw [he_v199]; exact empty_args) hinv190 h64 as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 dropping he_v199 hinv190 e_v199 s190
  store_step with Store.apply_rep s191 v199 v8 _ _ hinv191 h64 h_v199 h_v8 (by ns_tac) (by ns_tac) as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 dropping h_v199 hinv191 s191 v199
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s192 0#u32 (0) (by scalar_tac) hinv192 h64 as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 h_v200 dropping hinv192 s192
  store_step with Store.apply_rep s193 v200 v201 _ _ hinv193 h64 h_v200 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 dropping h_v200 h_v201 hinv193 s193 v200 v201
  step as ⟨e_v203, he_v203⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s194 e_v203 (by rw [he_v203]; exact empty_args) hinv194 h64 as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 h_v202 dropping he_v203 hinv194 e_v203 s194
  store_step with Store.apply_rep s195 v203 v8 _ _ hinv195 h64 h_v203 h_v8 (by ns_tac) (by ns_tac) as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 h_v202 dropping h_v203 hinv195 s195 v203
  store_step with Store.apply_rep s196 v204 v5 _ _ hinv196 h64 h_v204 h_v5 (by ns_tac) (by ns_tac) as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 h_v202 dropping h_v204 hinv196 s196 v204
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s197 0#u32 (0) (by scalar_tac) hinv197 h64 as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 h_v202 h_v205 dropping hinv197 s197
  store_step with Store.apply_rep s198 v205 v206 _ _ hinv198 h64 h_v205 h_v206 (by ns_tac) (by ns_tac) as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 h_v202 dropping h_v205 h_v206 hinv198 s198 v205 v206
  store_step with Store.apply_rep s199 v202 v207 _ _ hinv199 h64 h_v202 h_v207 (by ns_tac) (by ns_tac) as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 h_v198 dropping h_v202 h_v207 hinv199 s199 v202 v207
  store_step with Store.apply_rep s200 v198 v208 _ _ hinv200 h64 h_v198 h_v208 (by ns_tac) (by ns_tac) as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 h_v197 dropping h_v198 h_v208 hinv200 s200 v198 v208
  store_step with Store.apply_rep s201 v197 v209 _ _ hinv201 h64 h_v197 h_v209 (by ns_tac) (by ns_tac) as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v196 dropping h_v197 h_v209 hinv201 s201 v197 v209
  store_step with Store.apply_rep s202 v196 v210 _ _ hinv202 h64 h_v196 h_v210 (by ns_tac) (by ns_tac) as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 dropping h_v196 h_v210 hinv202 s202 v196 v210
  step as ⟨e_v212, he_v212⟩
  store_step with CtorSpec.eo__2b.construct s203 e_v212 (by rw [he_v212]; exact empty_args) hinv203 h64 as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v211 dropping he_v212 hinv203 e_v212 s203
  step as ⟨e_v213, he_v213⟩
  store_step with CtorSpec.eo_str_2elen.construct s204 e_v213 (by rw [he_v213]; exact empty_args) hinv204 h64 as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v211 h_v212 dropping he_v213 hinv204 e_v213 s204
  store_step with Store.apply_rep s205 v213 v5 _ _ hinv205 h64 h_v213 h_v5 (by ns_tac) (by ns_tac) as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v211 h_v212 dropping h_v213 hinv205 s205 v213
  store_step with Store.apply_rep s206 v212 v214 _ _ hinv206 h64 h_v212 h_v214 (by ns_tac) (by ns_tac) as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v211 dropping h_v212 h_v214 hinv206 s206 v212 v214
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s207 0#u32 (0) (by scalar_tac) hinv207 h64 as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v211 h_v215 dropping hinv207 s207
  store_step with Store.apply_rep s208 v215 v216 _ _ hinv208 h64 h_v215 h_v216 (by ns_tac) (by ns_tac) as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 h_v211 dropping h_v215 h_v216 hinv208 s208 v215 v216
  store_step with Store.apply_rep s209 v211 v217 _ _ hinv209 h64 h_v211 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 h_v195 dropping h_v211 h_v217 hinv209 s209 v211 v217
  store_step with Store.apply_rep s210 v195 v218 _ _ hinv210 h64 h_v195 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 h_v191 dropping h_v195 h_v218 hinv210 s210 v195 v218
  store_step with Store.apply_rep s211 v191 v219 _ _ hinv211 h64 h_v191 h_v219 (by ns_tac) (by ns_tac) as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 h_v165 dropping h_v191 h_v219 hinv211 s211 v191 v219
  store_step with Store.apply_rep s212 v165 v220 _ _ hinv212 h64 h_v165 h_v220 (by ns_tac) (by ns_tac) as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v164 dropping h_v165 h_v220 hinv212 s212 v165 v220
  store_step with Store.apply_rep s213 v164 v221 _ _ hinv213 h64 h_v164 h_v221 (by ns_tac) (by ns_tac) as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 dropping h_v164 h_v221 hinv213 s213 v164 v221
  step as ⟨e_v223, he_v223⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s214 e_v223 (by rw [he_v223]; exact empty_args) hinv214 h64 as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 dropping he_v223 hinv214 e_v223 s214
  step as ⟨e_v224, he_v224⟩
  store_step with CtorSpec.eo__40purify.construct s215 e_v224 (by rw [he_v224]; exact empty_args) hinv215 h64 as ⟨v224, s216, hinv216, h_v224⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 dropping he_v224 hinv215 e_v224 s215
  step as ⟨e_v225, he_v225⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s216 e_v225 (by rw [he_v225]; exact empty_args) hinv216 h64 as ⟨v225, s217, hinv217, h_v225⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 dropping he_v225 hinv216 e_v225 s216
  store_step with Store.apply_rep s217 v225 v8 _ _ hinv217 h64 h_v225 h_v8 (by ns_tac) (by ns_tac) as ⟨v226, s218, hinv218, h_v226⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 dropping h_v225 hinv217 s217 v225
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s218 0#u32 (0) (by scalar_tac) hinv218 h64 as ⟨v227, s219, hinv219, h_v227⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 h_v226 dropping hinv218 s218
  store_step with Store.apply_rep s219 v226 v227 _ _ hinv219 h64 h_v226 h_v227 (by ns_tac) (by ns_tac) as ⟨v228, s220, hinv220, h_v228⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 dropping h_v226 h_v227 hinv219 s219 v226 v227
  step as ⟨e_v229, he_v229⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s220 e_v229 (by rw [he_v229]; exact empty_args) hinv220 h64 as ⟨v229, s221, hinv221, h_v229⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 h_v228 dropping he_v229 hinv220 e_v229 s220
  store_step with Store.apply_rep s221 v229 v8 _ _ hinv221 h64 h_v229 h_v8 (by ns_tac) (by ns_tac) as ⟨v230, s222, hinv222, h_v230⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 h_v228 dropping h_v229 hinv221 s221 v229
  store_step with Store.apply_rep s222 v230 v5 _ _ hinv222 h64 h_v230 h_v5 (by ns_tac) (by ns_tac) as ⟨v231, s223, hinv223, h_v231⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 h_v228 dropping h_v230 hinv222 s222 v230
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s223 0#u32 (0) (by scalar_tac) hinv223 h64 as ⟨v232, s224, hinv224, h_v232⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 h_v228 h_v231 dropping hinv223 s223
  store_step with Store.apply_rep s224 v231 v232 _ _ hinv224 h64 h_v231 h_v232 (by ns_tac) (by ns_tac) as ⟨v233, s225, hinv225, h_v233⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 h_v228 dropping h_v231 h_v232 hinv224 s224 v231 v232
  store_step with Store.apply_rep s225 v228 v233 _ _ hinv225 h64 h_v228 h_v233 (by ns_tac) (by ns_tac) as ⟨v234, s226, hinv226, h_v234⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 h_v224 dropping h_v228 h_v233 hinv225 s225 v228 v233
  store_step with Store.apply_rep s226 v224 v234 _ _ hinv226 h64 h_v224 h_v234 (by ns_tac) (by ns_tac) as ⟨v235, s227, hinv227, h_v235⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 dropping h_v224 h_v234 hinv226 s226 v224 v234
  store_step with ih.eo__24eo_5ftypeof s227 v235 _ hinv227 h64 (hG.rem hrem) h_v235 as ⟨v236, s228, hinv228, h_v236⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 h_v223 dropping h_v235 hinv227 s227 v235
  store_step with ih.eo__24eo_5fnil s228 v223 v236 _ _ hinv228 h64 (hG.rem hrem) h_v223 h_v236 as ⟨v237, s229, hinv229, h_v237⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 h_v222 dropping h_v223 h_v236 hinv228 s228 v223 v236
  store_step with Store.apply_mk_rep s229 v222 v237 _ _ hinv229 h64 h_v222 h_v237 as ⟨v238, s230, hinv230, h_v238⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 h_v163 dropping h_v222 h_v237 hinv229 s229 v222 v237
  store_step with Store.apply_mk_rep s230 v163 v238 _ _ hinv230 h64 h_v163 h_v238 as ⟨v239, s231, hinv231, h_v239⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 h_v161 dropping h_v163 h_v238 hinv230 s230 v163 v238
  store_step with Store.apply_mk_rep s231 v161 v239 _ _ hinv231 h64 h_v161 h_v239 as ⟨v240, s232, hinv232, h_v240⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 h_v147 dropping h_v161 h_v239 hinv231 s231 v161 v239
  store_step with Store.apply_mk_rep s232 v147 v240 _ _ hinv232 h64 h_v147 h_v240 as ⟨v241, s233, hinv233, h_v241⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v139 dropping h_v147 h_v240 hinv232 s232 v147 v240
  store_step with Store.apply_mk_rep s233 v139 v241 _ _ hinv233 h64 h_v139 h_v241 as ⟨v242, s234, hinv234, h_v242⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 dropping h_v139 h_v241 hinv233 s233 v139 v241
  step as ⟨e_v243, he_v243⟩
  store_step with CtorSpec.eo_and.construct s234 e_v243 (by rw [he_v243]; exact empty_args) hinv234 h64 as ⟨v243, s235, hinv235, h_v243⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 dropping he_v243 hinv234 e_v243 s234
  step as ⟨e_v244, he_v244⟩
  store_step with CtorSpec.eo_not.construct s235 e_v244 (by rw [he_v244]; exact empty_args) hinv235 h64 as ⟨v244, s236, hinv236, h_v244⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 dropping he_v244 hinv235 e_v244 s235
  step as ⟨e_v245, he_v245⟩
  store_step with CtorSpec.eo_str_2econtains.construct s236 e_v245 (by rw [he_v245]; exact empty_args) hinv236 h64 as ⟨v245, s237, hinv237, h_v245⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 dropping he_v245 hinv236 e_v245 s236
  step as ⟨e_v246, he_v246⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s237 e_v246 (by rw [he_v246]; exact empty_args) hinv237 h64 as ⟨v246, s238, hinv238, h_v246⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 dropping he_v246 hinv237 e_v246 s237
  step as ⟨e_v247, he_v247⟩
  store_step with CtorSpec.eo__40purify.construct s238 e_v247 (by rw [he_v247]; exact empty_args) hinv238 h64 as ⟨v247, s239, hinv239, h_v247⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 dropping he_v247 hinv238 e_v247 s238
  step as ⟨e_v248, he_v248⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s239 e_v248 (by rw [he_v248]; exact empty_args) hinv239 h64 as ⟨v248, s240, hinv240, h_v248⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 dropping he_v248 hinv239 e_v248 s239
  store_step with Store.apply_rep s240 v248 v8 _ _ hinv240 h64 h_v248 h_v8 (by ns_tac) (by ns_tac) as ⟨v249, s241, hinv241, h_v249⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 dropping h_v248 hinv240 s240 v248
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s241 0#u32 (0) (by scalar_tac) hinv241 h64 as ⟨v250, s242, hinv242, h_v250⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 h_v249 dropping hinv241 s241
  store_step with Store.apply_rep s242 v249 v250 _ _ hinv242 h64 h_v249 h_v250 (by ns_tac) (by ns_tac) as ⟨v251, s243, hinv243, h_v251⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 dropping h_v249 h_v250 hinv242 s242 v249 v250
  step as ⟨e_v252, he_v252⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s243 e_v252 (by rw [he_v252]; exact empty_args) hinv243 h64 as ⟨v252, s244, hinv244, h_v252⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 h_v251 dropping he_v252 hinv243 e_v252 s243
  store_step with Store.apply_rep s244 v252 v8 _ _ hinv244 h64 h_v252 h_v8 (by ns_tac) (by ns_tac) as ⟨v253, s245, hinv245, h_v253⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 h_v251 dropping h_v252 hinv244 s244 v252
  store_step with Store.apply_rep s245 v253 v5 _ _ hinv245 h64 h_v253 h_v5 (by ns_tac) (by ns_tac) as ⟨v254, s246, hinv246, h_v254⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 h_v251 dropping h_v253 hinv245 s245 v253
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s246 0#u32 (0) (by scalar_tac) hinv246 h64 as ⟨v255, s247, hinv247, h_v255⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 h_v251 h_v254 dropping hinv246 s246
  store_step with Store.apply_rep s247 v254 v255 _ _ hinv247 h64 h_v254 h_v255 (by ns_tac) (by ns_tac) as ⟨v256, s248, hinv248, h_v256⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 h_v251 dropping h_v254 h_v255 hinv247 s247 v254 v255
  store_step with Store.apply_rep s248 v251 v256 _ _ hinv248 h64 h_v251 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s249, hinv249, h_v257⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 h_v247 dropping h_v251 h_v256 hinv248 s248 v251 v256
  store_step with Store.apply_rep s249 v247 v257 _ _ hinv249 h64 h_v247 h_v257 (by ns_tac) (by ns_tac) as ⟨v258, s250, hinv250, h_v258⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v246 dropping h_v247 h_v257 hinv249 s249 v247 v257
  store_step with Store.apply_rep s250 v246 v258 _ _ hinv250 h64 h_v246 h_v258 (by ns_tac) (by ns_tac) as ⟨v259, s251, hinv251, h_v259⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 dropping h_v246 h_v258 hinv250 s250 v246 v258
  step as ⟨e_v260, he_v260⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s251 e_v260 (by rw [he_v260]; exact empty_args) hinv251 h64 as ⟨v260, s252, hinv252, h_v260⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 dropping he_v260 hinv251 e_v260 s251
  step as ⟨e_v261, he_v261⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s252 e_v261 (by rw [he_v261]; exact empty_args) hinv252 h64 as ⟨v261, s253, hinv253, h_v261⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 dropping he_v261 hinv252 e_v261 s252
  store_step with Store.apply_rep s253 v261 v5 _ _ hinv253 h64 h_v261 h_v5 (by ns_tac) (by ns_tac) as ⟨v262, s254, hinv254, h_v262⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 dropping h_v261 hinv253 s253 v261
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s254 0#u32 (0) (by scalar_tac) hinv254 h64 as ⟨v263, s255, hinv255, h_v263⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v262 dropping hinv254 s254
  store_step with Store.apply_rep s255 v262 v263 _ _ hinv255 h64 h_v262 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s256, hinv256, h_v264⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 dropping h_v262 h_v263 hinv255 s255 v262 v263
  step as ⟨e_v265, he_v265⟩
  store_step with CtorSpec.eo__2d.construct s256 e_v265 (by rw [he_v265]; exact empty_args) hinv256 h64 as ⟨v265, s257, hinv257, h_v265⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v264 dropping he_v265 hinv256 e_v265 s256
  step as ⟨e_v266, he_v266⟩
  store_step with CtorSpec.eo_str_2elen.construct s257 e_v266 (by rw [he_v266]; exact empty_args) hinv257 h64 as ⟨v266, s258, hinv258, h_v266⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v264 h_v265 dropping he_v266 hinv257 e_v266 s257
  store_step with Store.apply_rep s258 v266 v5 _ _ hinv258 h64 h_v266 h_v5 (by ns_tac) (by ns_tac) as ⟨v267, s259, hinv259, h_v267⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v264 h_v265 dropping h_v266 hinv258 s258 v266
  store_step with Store.apply_rep s259 v265 v267 _ _ hinv259 h64 h_v265 h_v267 (by ns_tac) (by ns_tac) as ⟨v268, s260, hinv260, h_v268⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v264 dropping h_v265 h_v267 hinv259 s259 v265 v267
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s260 1#u32 (1) (by scalar_tac) hinv260 h64 as ⟨v269, s261, hinv261, h_v269⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v264 h_v268 dropping hinv260 s260
  store_step with Store.apply_rep s261 v268 v269 _ _ hinv261 h64 h_v268 h_v269 (by ns_tac) (by ns_tac) as ⟨v270, s262, hinv262, h_v270⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 h_v264 dropping h_v268 h_v269 hinv261 s261 v268 v269
  store_step with Store.apply_rep s262 v264 v270 _ _ hinv262 h64 h_v264 h_v270 (by ns_tac) (by ns_tac) as ⟨v271, s263, hinv263, h_v271⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v260 dropping h_v264 h_v270 hinv262 s262 v264 v270
  store_step with Store.apply_rep s263 v260 v271 _ _ hinv263 h64 h_v260 h_v271 (by ns_tac) (by ns_tac) as ⟨v272, s264, hinv264, h_v272⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 dropping h_v260 h_v271 hinv263 s263 v260 v271
  step as ⟨e_v273, he_v273⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s264 e_v273 (by rw [he_v273]; exact empty_args) hinv264 h64 as ⟨v273, s265, hinv265, h_v273⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 dropping he_v273 hinv264 e_v273 s264
  step as ⟨e_v274, he_v274⟩
  store_step with CtorSpec.eo__40purify.construct s265 e_v274 (by rw [he_v274]; exact empty_args) hinv265 h64 as ⟨v274, s266, hinv266, h_v274⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 dropping he_v274 hinv265 e_v274 s265
  step as ⟨e_v275, he_v275⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s266 e_v275 (by rw [he_v275]; exact empty_args) hinv266 h64 as ⟨v275, s267, hinv267, h_v275⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 dropping he_v275 hinv266 e_v275 s266
  store_step with Store.apply_rep s267 v275 v8 _ _ hinv267 h64 h_v275 h_v8 (by ns_tac) (by ns_tac) as ⟨v276, s268, hinv268, h_v276⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 dropping h_v275 hinv267 s267 v275
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s268 0#u32 (0) (by scalar_tac) hinv268 h64 as ⟨v277, s269, hinv269, h_v277⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 h_v276 dropping hinv268 s268
  store_step with Store.apply_rep s269 v276 v277 _ _ hinv269 h64 h_v276 h_v277 (by ns_tac) (by ns_tac) as ⟨v278, s270, hinv270, h_v278⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 dropping h_v276 h_v277 hinv269 s269 v276 v277
  step as ⟨e_v279, he_v279⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s270 e_v279 (by rw [he_v279]; exact empty_args) hinv270 h64 as ⟨v279, s271, hinv271, h_v279⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 h_v278 dropping he_v279 hinv270 e_v279 s270
  store_step with Store.apply_rep s271 v279 v8 _ _ hinv271 h64 h_v279 h_v8 (by ns_tac) (by ns_tac) as ⟨v280, s272, hinv272, h_v280⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 h_v278 dropping h_v279 hinv271 s271 v279
  store_step with Store.apply_rep s272 v280 v5 _ _ hinv272 h64 h_v280 h_v5 (by ns_tac) (by ns_tac) as ⟨v281, s273, hinv273, h_v281⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 h_v278 dropping h_v280 hinv272 s272 v280
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s273 0#u32 (0) (by scalar_tac) hinv273 h64 as ⟨v282, s274, hinv274, h_v282⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 h_v278 h_v281 dropping hinv273 s273
  store_step with Store.apply_rep s274 v281 v282 _ _ hinv274 h64 h_v281 h_v282 (by ns_tac) (by ns_tac) as ⟨v283, s275, hinv275, h_v283⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 h_v278 dropping h_v281 h_v282 hinv274 s274 v281 v282
  store_step with Store.apply_rep s275 v278 v283 _ _ hinv275 h64 h_v278 h_v283 (by ns_tac) (by ns_tac) as ⟨v284, s276, hinv276, h_v284⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 h_v274 dropping h_v278 h_v283 hinv275 s275 v278 v283
  store_step with Store.apply_rep s276 v274 v284 _ _ hinv276 h64 h_v274 h_v284 (by ns_tac) (by ns_tac) as ⟨v285, s277, hinv277, h_v285⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 dropping h_v274 h_v284 hinv276 s276 v274 v284
  store_step with ih.eo__24eo_5ftypeof s277 v285 _ hinv277 h64 (hG.rem hrem) h_v285 as ⟨v286, s278, hinv278, h_v286⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 h_v273 dropping h_v285 hinv277 s277 v285
  store_step with ih.eo__24eo_5fnil s278 v273 v286 _ _ hinv278 h64 (hG.rem hrem) h_v273 h_v286 as ⟨v287, s279, hinv279, h_v287⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 h_v272 dropping h_v273 h_v286 hinv278 s278 v273 v286
  store_step with Store.apply_mk_rep s279 v272 v287 _ _ hinv279 h64 h_v272 h_v287 as ⟨v288, s280, hinv280, h_v288⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 h_v259 dropping h_v272 h_v287 hinv279 s279 v272 v287
  store_step with Store.apply_mk_rep s280 v259 v288 _ _ hinv280 h64 h_v259 h_v288 as ⟨v289, s281, hinv281, h_v289⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 h_v245 dropping h_v259 h_v288 hinv280 s280 v259 v288
  store_step with Store.apply_mk_rep s281 v245 v289 _ _ hinv281 h64 h_v245 h_v289 as ⟨v290, s282, hinv282, h_v290⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 dropping h_v245 h_v289 hinv281 s281 v245 v289
  store_step with Store.apply_mk_rep s282 v290 v5 _ _ hinv282 h64 h_v290 h_v5 as ⟨v291, s283, hinv283, h_v291⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 h_v244 dropping h_v290 hinv282 s282 v290
  store_step with Store.apply_mk_rep s283 v244 v291 _ _ hinv283 h64 h_v244 h_v291 as ⟨v292, s284, hinv284, h_v292⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v243 dropping h_v244 h_v291 hinv283 s283 v244 v291
  store_step with Store.apply_mk_rep s284 v243 v292 _ _ hinv284 h64 h_v243 h_v292 as ⟨v293, s285, hinv285, h_v293⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 dropping h_v243 h_v292 hinv284 s284 v243 v292
  store_step with Store.literal_boolean_spec s285 true hinv285 h64 as ⟨v294, s286, hinv286, h_v294⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 h_v293 dropping hinv285 s285
  store_step with Store.apply_mk_rep s286 v293 v294 _ _ hinv286 h64 h_v293 h_v294 as ⟨v295, s287, hinv287, h_v295⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 h_v242 dropping h_v293 h_v294 hinv286 s286 v293 v294
  store_step with Store.apply_mk_rep s287 v242 v295 _ _ hinv287 h64 h_v242 h_v295 as ⟨v296, s288, hinv288, h_v296⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 h_v138 dropping h_v242 h_v295 hinv287 s287 v242 v295
  store_step with Store.apply_mk_rep s288 v138 v296 _ _ hinv288 h64 h_v138 h_v296 as ⟨v297, s289, hinv289, h_v297⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v40 dropping h_v138 h_v296 hinv288 s288 v138 v296
  store_step with Store.apply_mk_rep s289 v40 v297 _ _ hinv289 h64 h_v40 h_v297 as ⟨v298, s290, hinv290, h_v298⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 dropping h_v297 h_v40 hinv289 s289 v297 v40
  step as ⟨e_v299, he_v299⟩
  store_step with CtorSpec.eo__3d.construct s290 e_v299 (by rw [he_v299]; exact empty_args) hinv290 h64 as ⟨v299, s291, hinv291, h_v299⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v298 dropping he_v299 hinv290 e_v299 s290
  step as ⟨e_v300, he_v300⟩
  store_step with CtorSpec.eo__40purify.construct s291 e_v300 (by rw [he_v300]; exact empty_args) hinv291 h64 as ⟨v300, s292, hinv292, h_v300⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v298 h_v299 dropping he_v300 hinv291 e_v300 s291
  step as ⟨e_v301, he_v301⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s292 e_v301 (by rw [he_v301]; exact empty_args) hinv292 h64 as ⟨v301, s293, hinv293, h_v301⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v298 h_v299 h_v300 dropping he_v301 hinv292 e_v301 s292
  store_step with Store.apply_rep s293 v301 v8 _ _ hinv293 h64 h_v301 h_v8 (by ns_tac) (by ns_tac) as ⟨v302, s294, hinv294, h_v302⟩ growing hG carrying h_v2 h_v5 h_v8 h_v35 h_v298 h_v299 h_v300 dropping h_v301 hinv293 s293 v301
  store_step with Store.apply_rep s294 v302 v5 _ _ hinv294 h64 h_v302 h_v5 (by ns_tac) (by ns_tac) as ⟨v303, s295, hinv295, h_v303⟩ growing hG carrying h_v2 h_v8 h_v35 h_v298 h_v299 h_v300 dropping h_v302 h_v5 hinv294 s294 v302 v5
  store_step with Store.apply_rep s295 v303 v2 _ _ hinv295 h64 h_v303 h_v2 (by ns_tac) (by ns_tac) as ⟨v304, s296, hinv296, h_v304⟩ growing hG carrying h_v8 h_v35 h_v298 h_v299 h_v300 dropping h_v2 h_v303 hinv295 s295 v2 v303
  store_step with Store.apply_rep s296 v300 v304 _ _ hinv296 h64 h_v300 h_v304 (by ns_tac) (by ns_tac) as ⟨v305, s297, hinv297, h_v305⟩ growing hG carrying h_v8 h_v35 h_v298 h_v299 dropping h_v300 h_v304 hinv296 s296 v300 v304
  store_step with Store.apply_rep s297 v299 v305 _ _ hinv297 h64 h_v299 h_v305 (by ns_tac) (by ns_tac) as ⟨v306, s298, hinv298, h_v306⟩ growing hG carrying h_v8 h_v35 h_v298 dropping h_v299 h_v305 hinv297 s297 v299 v305
  store_step with Store.apply_rep s298 v306 v8 _ _ hinv298 h64 h_v306 h_v8 (by ns_tac) (by ns_tac) as ⟨v307, s299, hinv299, h_v307⟩ growing hG carrying h_v35 h_v298 dropping h_v306 h_v8 hinv298 s298 v306 v8
  store_step with Store.apply_mk_rep s299 v298 v307 _ _ hinv299 h64 h_v298 h_v307 as ⟨v308, s300, hinv300, h_v308⟩ growing hG carrying h_v35 dropping h_v298 h_v307 hinv299 s299 v298 v307
  store_step with Store.apply_mk_rep s300 v35 v308 _ _ hinv300 h64 h_v35 h_v308 as ⟨v309, s301, hinv301, h_v309⟩ growing hG carrying dropping h_v308 h_v35 hinv300 s300 v308 v35
  case_done hinv301 hG with h_v309 in EoCases.__str_reduction_pred.case_3 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

end pathos_compiled_checker
