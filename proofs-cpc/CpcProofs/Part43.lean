module
public import CpcProofs.Head
public import CpcProofs.Part42
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

set_option maxHeartbeats 7980000 in
theorem case_11_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_11_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_11 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_11
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_11
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_11
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_11
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3e.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with Store.apply_rep s4 v12 v2 _ _ hinv4 h64 h_v12 h_v2 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v12 hinv4 s4 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2elen.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 dropping he_v14 hinv5 e_v14 s5
  store_step with Store.apply_rep s6 v14 v8 _ _ hinv6 h64 h_v14 h_v8 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 dropping h_v14 hinv6 s6 v14
  store_step with Store.apply_rep s7 v13 v15 _ _ hinv7 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v13 h_v15 hinv7 s7 v13 v15
  store_step with Store.apply_rep s8 v11 v16 _ _ hinv8 h64 h_v11 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 h_v16 hinv8 s8 v11 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_or.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 dropping he_v18 hinv9 e_v18 s9
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3e.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 h_v18 dropping he_v19 hinv10 e_v19 s10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 h_v18 h_v19 dropping hinv11 s11
  store_step with Store.apply_rep s12 v19 v20 _ _ hinv12 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 h_v18 dropping h_v19 h_v20 hinv12 s12 v19 v20
  store_step with Store.apply_rep s13 v21 v2 _ _ hinv13 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 h_v18 dropping h_v21 hinv13 s13 v21
  store_step with Store.apply_rep s14 v18 v22 _ _ hinv14 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 dropping h_v18 h_v22 hinv14 s14 v18 v22
  store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 h_v23 dropping hinv15 s15
  store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v17 dropping h_v23 h_v24 hinv16 s16 v23 v24
  store_step with Store.apply_rep s17 v17 v25 _ _ hinv17 h64 h_v17 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v17 h_v25 hinv17 s17 v17 v25
  store_step with Store.apply_rep s18 v10 v26 _ _ hinv18 h64 h_v10 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v26 hinv18 s18 v10 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__3d.construct s19 e_v28 (by rw [he_v28]; exact empty_args) hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 dropping he_v28 hinv19 e_v28 s19
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__40purify.construct s20 e_v29 (by rw [he_v29]; exact empty_args) hinv20 h64 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 dropping he_v29 hinv20 e_v29 s20
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s21 e_v30 (by rw [he_v30]; exact empty_args) hinv21 h64 as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 dropping he_v30 hinv21 e_v30 s21
  store_step with Store.apply_rep s22 v30 v8 _ _ hinv22 h64 h_v30 h_v8 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 dropping h_v30 hinv22 s22 v30
  store_step with Store.apply_rep s23 v31 v5 _ _ hinv23 h64 h_v31 h_v5 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 dropping h_v31 hinv23 s23 v31
  store_step with Store.apply_rep s24 v32 v2 _ _ hinv24 h64 h_v32 h_v2 (by ns_tac) (by ns_tac) as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 dropping h_v32 hinv24 s24 v32
  store_step with Store.apply_rep s25 v29 v33 _ _ hinv25 h64 h_v29 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 dropping h_v29 h_v33 hinv25 s25 v29 v33
  store_step with Store.apply_rep s26 v28 v34 _ _ hinv26 h64 h_v28 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 dropping h_v28 h_v34 hinv26 s26 v28 v34
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s27 1#u32 (-1) (by scalar_tac) hinv27 h64 as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v35 dropping hinv27 s27
  store_step with Store.apply_rep s28 v35 v36 _ _ hinv28 h64 h_v35 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 dropping h_v35 h_v36 hinv28 s28 v35 v36
  store_step with Store.apply_rep s29 v27 v37 _ _ hinv29 h64 h_v27 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v27 h_v37 hinv29 s29 v27 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_ite.construct s30 e_v39 (by rw [he_v39]; exact empty_args) hinv30 h64 as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 dropping he_v39 hinv30 e_v39 s30
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s31 e_v40 (by rw [he_v40]; exact empty_args) hinv31 h64 as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v39 dropping he_v40 hinv31 e_v40 s31
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s32 _ _ rfl hinv32 h64 as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v39 h_v40 dropping hinv32 s32
  store_step with Store.apply_rep s33 v40 v41 _ _ hinv33 h64 h_v40 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v39 dropping h_v40 h_v41 hinv33 s33 v40 v41
  store_step with Store.apply_rep s34 v42 v5 _ _ hinv34 h64 h_v42 h_v5 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v39 dropping h_v42 hinv34 s34 v42
  store_step with Store.apply_rep s35 v39 v43 _ _ hinv35 h64 h_v39 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 dropping h_v39 h_v43 hinv35 s35 v39 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__3d.construct s36 e_v45 (by rw [he_v45]; exact empty_args) hinv36 h64 as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 dropping he_v45 hinv36 e_v45 s36
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__40purify.construct s37 e_v46 (by rw [he_v46]; exact empty_args) hinv37 h64 as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 h_v45 dropping he_v46 hinv37 e_v46 s37
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s38 e_v47 (by rw [he_v47]; exact empty_args) hinv38 h64 as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 h_v45 h_v46 dropping he_v47 hinv38 e_v47 s38
  store_step with Store.apply_rep s39 v47 v8 _ _ hinv39 h64 h_v47 h_v8 (by ns_tac) (by ns_tac) as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 h_v45 h_v46 dropping h_v47 hinv39 s39 v47
  store_step with Store.apply_rep s40 v48 v5 _ _ hinv40 h64 h_v48 h_v5 (by ns_tac) (by ns_tac) as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 h_v45 h_v46 dropping h_v48 hinv40 s40 v48
  store_step with Store.apply_rep s41 v49 v2 _ _ hinv41 h64 h_v49 h_v2 (by ns_tac) (by ns_tac) as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 h_v45 h_v46 dropping h_v49 hinv41 s41 v49
  store_step with Store.apply_rep s42 v46 v50 _ _ hinv42 h64 h_v46 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 h_v45 dropping h_v46 h_v50 hinv42 s42 v46 v50
  store_step with Store.apply_rep s43 v45 v51 _ _ hinv43 h64 h_v45 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 dropping h_v45 h_v51 hinv43 s43 v45 v51
  store_step with Store.apply_rep s44 v52 v2 _ _ hinv44 h64 h_v52 h_v2 (by ns_tac) (by ns_tac) as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v44 dropping h_v52 hinv44 s44 v52
  store_step with Store.apply_rep s45 v44 v53 _ _ hinv45 h64 h_v44 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 dropping h_v44 h_v53 hinv45 s45 v44 v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_and.construct s46 e_v55 (by rw [he_v55]; exact empty_args) hinv46 h64 as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 dropping he_v55 hinv46 e_v55 s46
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_forall.construct s47 e_v56 (by rw [he_v56]; exact empty_args) hinv47 h64 as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 dropping he_v56 hinv47 e_v56 s47
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s48 e_v57 (by rw [he_v57]; exact empty_args) hinv48 h64 as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 dropping he_v57 hinv48 e_v57 s48
  step as ⟨e_v58, he_v58⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s49 _ _ rfl hinv49 h64 as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v57 dropping hinv49 s49
  replace h_v58 := Represents.rep_of_eq h_v58 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v58]; decide)
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo_Int.construct s50 e_v59 (by rw [he_v59]; exact empty_args) hinv50 h64 as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v57 h_v58 dropping he_v58 he_v59 hinv50 e_v58 e_v59 s50
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s51 e_v60 (by rw [he_v60]; rfl) h_v58 h_v59 hinv51 h64 as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v57 dropping h_v58 h_v59 he_v60 hinv51 e_v60 s51 v58 v59
  store_step with Store.apply_rep s52 v57 v60 _ _ hinv52 h64 h_v57 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 dropping h_v57 h_v60 hinv52 s52 v57 v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s53 e_v62 (by rw [he_v62]; exact empty_args) hinv53 h64 as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 dropping he_v62 hinv53 e_v62 s53
  step as ⟨e_v63, he_v63⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s54 _ _ rfl hinv54 h64 as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 h_v62 dropping hinv54 s54
  replace h_v63 := Represents.rep_of_eq h_v63 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v63]; decide)
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_Int.construct s55 e_v64 (by rw [he_v64]; exact empty_args) hinv55 h64 as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 h_v62 h_v63 dropping he_v63 he_v64 hinv55 e_v63 e_v64 s55
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s56 e_v65 (by rw [he_v65]; rfl) h_v63 h_v64 hinv56 h64 as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 h_v62 dropping h_v63 h_v64 he_v65 hinv56 e_v65 s56 v63 v64
  store_step with Store.apply_rep s57 v62 v65 _ _ hinv57 h64 h_v62 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 dropping h_v62 h_v65 hinv57 s57 v62 v65
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s58 e_v67 (by rw [he_v67]; exact empty_args) hinv58 h64 as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 h_v66 dropping he_v67 hinv58 e_v67 s58
  store_step with Store.apply_rep s59 v66 v67 _ _ hinv59 h64 h_v66 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 h_v61 dropping h_v66 h_v67 hinv59 s59 v66 v67
  store_step with Store.apply_rep s60 v61 v68 _ _ hinv60 h64 h_v61 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v56 dropping h_v61 h_v68 hinv60 s60 v61 v68
  store_step with Store.apply_rep s61 v56 v69 _ _ hinv61 h64 h_v56 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 dropping h_v56 h_v69 hinv61 s61 v56 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_or.construct s62 e_v71 (by rw [he_v71]; exact empty_args) hinv62 h64 as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 dropping he_v71 hinv62 e_v71 s62
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo_not.construct s63 e_v72 (by rw [he_v72]; exact empty_args) hinv63 h64 as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 dropping he_v72 hinv63 e_v72 s63
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo__3e_3d.construct s64 e_v73 (by rw [he_v73]; exact empty_args) hinv64 h64 as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 h_v72 dropping he_v73 hinv64 e_v73 s64
  step as ⟨e_v74, he_v74⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s65 _ _ rfl hinv65 h64 as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 h_v72 h_v73 dropping hinv65 s65
  replace h_v74 := Represents.rep_of_eq h_v74 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v74]; decide)
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_Int.construct s66 e_v75 (by rw [he_v75]; exact empty_args) hinv66 h64 as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 h_v72 h_v73 h_v74 dropping he_v74 he_v75 hinv66 e_v74 e_v75 s66
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s67 e_v76 (by rw [he_v76]; rfl) h_v74 h_v75 hinv67 h64 as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 h_v72 h_v73 dropping h_v74 h_v75 he_v76 hinv67 e_v76 s67 v74 v75
  store_step with Store.apply_rep s68 v73 v76 _ _ hinv68 h64 h_v73 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 h_v72 dropping h_v73 h_v76 hinv68 s68 v73 v76
  store_step with Store.apply_rep s69 v77 v2 _ _ hinv69 h64 h_v77 h_v2 (by ns_tac) (by ns_tac) as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 h_v72 dropping h_v77 hinv69 s69 v77
  store_step with Store.apply_rep s70 v72 v78 _ _ hinv70 h64 h_v72 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v71 dropping h_v72 h_v78 hinv70 s70 v72 v78
  store_step with Store.apply_rep s71 v71 v79 _ _ hinv71 h64 h_v71 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 dropping h_v71 h_v79 hinv71 s71 v71 v79
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo_or.construct s72 e_v81 (by rw [he_v81]; exact empty_args) hinv72 h64 as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 dropping he_v81 hinv72 e_v81 s72
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo_not.construct s73 e_v82 (by rw [he_v82]; exact empty_args) hinv73 h64 as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 dropping he_v82 hinv73 e_v82 s73
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo__3c.construct s74 e_v83 (by rw [he_v83]; exact empty_args) hinv74 h64 as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 dropping he_v83 hinv74 e_v83 s74
  step as ⟨e_v84, he_v84⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s75 _ _ rfl hinv75 h64 as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v83 dropping hinv75 s75
  replace h_v84 := Represents.rep_of_eq h_v84 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v84]; decide)
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_Int.construct s76 e_v85 (by rw [he_v85]; exact empty_args) hinv76 h64 as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v83 h_v84 dropping he_v84 he_v85 hinv76 e_v84 e_v85 s76
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s77 e_v86 (by rw [he_v86]; rfl) h_v84 h_v85 hinv77 h64 as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v83 dropping h_v84 h_v85 he_v86 hinv77 e_v86 s77 v84 v85
  store_step with Store.apply_rep s78 v83 v86 _ _ hinv78 h64 h_v83 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 dropping h_v83 h_v86 hinv78 s78 v83 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_ite.construct s79 e_v88 (by rw [he_v88]; exact empty_args) hinv79 h64 as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 dropping he_v88 hinv79 e_v88 s79
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo__3d.construct s80 e_v89 (by rw [he_v89]; exact empty_args) hinv80 h64 as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 dropping he_v89 hinv80 e_v89 s80
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo__40purify.construct s81 e_v90 (by rw [he_v90]; exact empty_args) hinv81 h64 as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v89 dropping he_v90 hinv81 e_v90 s81
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s82 e_v91 (by rw [he_v91]; exact empty_args) hinv82 h64 as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v89 h_v90 dropping he_v91 hinv82 e_v91 s82
  store_step with Store.apply_rep s83 v91 v8 _ _ hinv83 h64 h_v91 h_v8 (by ns_tac) (by ns_tac) as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v89 h_v90 dropping h_v91 hinv83 s83 v91
  store_step with Store.apply_rep s84 v92 v5 _ _ hinv84 h64 h_v92 h_v5 (by ns_tac) (by ns_tac) as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v89 h_v90 dropping h_v92 hinv84 s84 v92
  store_step with Store.apply_rep s85 v93 v2 _ _ hinv85 h64 h_v93 h_v2 (by ns_tac) (by ns_tac) as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v89 h_v90 dropping h_v93 hinv85 s85 v93
  store_step with Store.apply_rep s86 v90 v94 _ _ hinv86 h64 h_v90 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v89 dropping h_v90 h_v94 hinv86 s86 v90 v94
  store_step with Store.apply_rep s87 v89 v95 _ _ hinv87 h64 h_v89 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 dropping h_v89 h_v95 hinv87 s87 v89 v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s88 1#u32 (-1) (by scalar_tac) hinv88 h64 as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 h_v96 dropping hinv88 s88
  store_step with Store.apply_rep s89 v96 v97 _ _ hinv89 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v88 dropping h_v96 h_v97 hinv89 s89 v96 v97
  store_step with Store.apply_rep s90 v88 v98 _ _ hinv90 h64 h_v88 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 dropping h_v88 h_v98 hinv90 s90 v88 v98
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_str_2elen.construct s91 e_v100 (by rw [he_v100]; exact empty_args) hinv91 h64 as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v99 dropping he_v100 hinv91 e_v100 s91
  store_step with Store.apply_rep s92 v100 v8 _ _ hinv92 h64 h_v100 h_v8 (by ns_tac) (by ns_tac) as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v99 dropping h_v100 hinv92 s92 v100
  store_step with Store.apply_rep s93 v99 v101 _ _ hinv93 h64 h_v99 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 dropping h_v101 h_v99 hinv93 s93 v101 v99
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo__40purify.construct s94 e_v103 (by rw [he_v103]; exact empty_args) hinv94 h64 as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v102 dropping he_v103 hinv94 e_v103 s94
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s95 e_v104 (by rw [he_v104]; exact empty_args) hinv95 h64 as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v102 h_v103 dropping he_v104 hinv95 e_v104 s95
  store_step with Store.apply_rep s96 v104 v8 _ _ hinv96 h64 h_v104 h_v8 (by ns_tac) (by ns_tac) as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v102 h_v103 dropping h_v104 hinv96 s96 v104
  store_step with Store.apply_rep s97 v105 v5 _ _ hinv97 h64 h_v105 h_v5 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v102 h_v103 dropping h_v105 hinv97 s97 v105
  store_step with Store.apply_rep s98 v106 v2 _ _ hinv98 h64 h_v106 h_v2 (by ns_tac) (by ns_tac) as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v102 h_v103 dropping h_v106 hinv98 s98 v106
  store_step with Store.apply_rep s99 v103 v107 _ _ hinv99 h64 h_v103 h_v107 (by ns_tac) (by ns_tac) as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 h_v102 dropping h_v103 h_v107 hinv99 s99 v103 v107
  store_step with Store.apply_rep s100 v102 v108 _ _ hinv100 h64 h_v102 h_v108 (by ns_tac) (by ns_tac) as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 h_v87 dropping h_v102 h_v108 hinv100 s100 v102 v108
  store_step with Store.apply_rep s101 v87 v109 _ _ hinv101 h64 h_v87 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 h_v82 dropping h_v109 h_v87 hinv101 s101 v109 v87
  store_step with Store.apply_rep s102 v82 v110 _ _ hinv102 h64 h_v82 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v81 dropping h_v110 h_v82 hinv102 s102 v110 v82
  store_step with Store.apply_rep s103 v81 v111 _ _ hinv103 h64 h_v81 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 dropping h_v111 h_v81 hinv103 s103 v111 v81
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_or.construct s104 e_v113 (by rw [he_v113]; exact empty_args) hinv104 h64 as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 dropping he_v113 hinv104 e_v113 s104
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_not.construct s105 e_v114 (by rw [he_v114]; exact empty_args) hinv105 h64 as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 dropping he_v114 hinv105 e_v114 s105
  step as ⟨e_v115, he_v115⟩
  store_step with CtorSpec.eo__3e.construct s106 e_v115 (by rw [he_v115]; exact empty_args) hinv106 h64 as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 dropping he_v115 hinv106 e_v115 s106
  step as ⟨e_v116, he_v116⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s107 _ _ rfl hinv107 h64 as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 h_v115 dropping hinv107 s107
  replace h_v116 := Represents.rep_of_eq h_v116 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v116]; decide)
  step as ⟨e_v117, he_v117⟩
  store_step with CtorSpec.eo_Int.construct s108 e_v117 (by rw [he_v117]; exact empty_args) hinv108 h64 as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 h_v115 h_v116 dropping he_v116 he_v117 hinv108 e_v116 e_v117 s108
  step as ⟨e_v118, he_v118⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s109 e_v118 (by rw [he_v118]; rfl) h_v116 h_v117 hinv109 h64 as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 h_v115 dropping h_v116 h_v117 he_v118 hinv109 e_v118 s109 v116 v117
  store_step with Store.apply_rep s110 v115 v118 _ _ hinv110 h64 h_v115 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 dropping h_v115 h_v118 hinv110 s110 v115 v118
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s111 0#u32 (0) (by scalar_tac) hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 h_v119 dropping hinv111 s111
  store_step with Store.apply_rep s112 v119 v120 _ _ hinv112 h64 h_v119 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 h_v114 dropping h_v119 h_v120 hinv112 s112 v119 v120
  store_step with Store.apply_rep s113 v114 v121 _ _ hinv113 h64 h_v114 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v113 dropping h_v114 h_v121 hinv113 s113 v114 v121
  store_step with Store.apply_rep s114 v113 v122 _ _ hinv114 h64 h_v113 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 dropping h_v113 h_v122 hinv114 s114 v113 v122
  step as ⟨e_v124, he_v124⟩
  store_step with CtorSpec.eo_or.construct s115 e_v124 (by rw [he_v124]; exact empty_args) hinv115 h64 as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 dropping he_v124 hinv115 e_v124 s115
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo_not.construct s116 e_v125 (by rw [he_v125]; exact empty_args) hinv116 h64 as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 dropping he_v125 hinv116 e_v125 s116
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo__3c_3d.construct s117 e_v126 (by rw [he_v126]; exact empty_args) hinv117 h64 as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 dropping he_v126 hinv117 e_v126 s117
  step as ⟨e_v127, he_v127⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s118 _ _ rfl hinv118 h64 as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v126 dropping hinv118 s118
  replace h_v127 := Represents.rep_of_eq h_v127 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v127]; decide)
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo_Int.construct s119 e_v128 (by rw [he_v128]; exact empty_args) hinv119 h64 as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v126 h_v127 dropping he_v127 he_v128 hinv119 e_v127 e_v128 s119
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s120 e_v129 (by rw [he_v129]; rfl) h_v127 h_v128 hinv120 h64 as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v126 dropping h_v127 h_v128 he_v129 hinv120 e_v129 s120 v127 v128
  store_step with Store.apply_rep s121 v126 v129 _ _ hinv121 h64 h_v126 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 dropping h_v126 h_v129 hinv121 s121 v126 v129
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo__2d.construct s122 e_v131 (by rw [he_v131]; exact empty_args) hinv122 h64 as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 dropping he_v131 hinv122 e_v131 s122
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo_str_2elen.construct s123 e_v132 (by rw [he_v132]; exact empty_args) hinv123 h64 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 h_v131 dropping he_v132 hinv123 e_v132 s123
  store_step with Store.apply_rep s124 v132 v8 _ _ hinv124 h64 h_v132 h_v8 (by ns_tac) (by ns_tac) as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 h_v131 dropping h_v132 hinv124 s124 v132
  store_step with Store.apply_rep s125 v131 v133 _ _ hinv125 h64 h_v131 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 dropping h_v131 h_v133 hinv125 s125 v131 v133
  step as ⟨e_v135, he_v135⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s126 _ _ rfl hinv126 h64 as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 h_v134 dropping hinv126 s126
  replace h_v135 := Represents.rep_of_eq h_v135 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v135]; decide)
  step as ⟨e_v136, he_v136⟩
  store_step with CtorSpec.eo_Int.construct s127 e_v136 (by rw [he_v136]; exact empty_args) hinv127 h64 as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 h_v134 h_v135 dropping he_v135 he_v136 hinv127 e_v135 e_v136 s127
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s128 e_v137 (by rw [he_v137]; rfl) h_v135 h_v136 hinv128 h64 as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 h_v134 dropping h_v135 h_v136 he_v137 hinv128 e_v137 s128 v135 v136
  store_step with Store.apply_rep s129 v134 v137 _ _ hinv129 h64 h_v134 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 h_v130 dropping h_v134 h_v137 hinv129 s129 v134 v137
  store_step with Store.apply_rep s130 v130 v138 _ _ hinv130 h64 h_v130 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 h_v125 dropping h_v130 h_v138 hinv130 s130 v130 v138
  store_step with Store.apply_rep s131 v125 v139 _ _ hinv131 h64 h_v125 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v124 dropping h_v125 h_v139 hinv131 s131 v125 v139
  store_step with Store.apply_rep s132 v124 v140 _ _ hinv132 h64 h_v124 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 dropping h_v124 h_v140 hinv132 s132 v124 v140
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo_or.construct s133 e_v142 (by rw [he_v142]; exact empty_args) hinv133 h64 as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 dropping he_v142 hinv133 e_v142 s133
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_not.construct s134 e_v143 (by rw [he_v143]; exact empty_args) hinv134 h64 as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 dropping he_v143 hinv134 e_v143 s134
  step as ⟨e_v144, he_v144⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s135 e_v144 (by rw [he_v144]; exact empty_args) hinv135 h64 as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 dropping he_v144 hinv135 e_v144 s135
  step as ⟨e_v145, he_v145⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s136 e_v145 (by rw [he_v145]; exact empty_args) hinv136 h64 as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 dropping he_v145 hinv136 e_v145 s136
  store_step with Store.apply_rep s137 v145 v8 _ _ hinv137 h64 h_v145 h_v8 (by ns_tac) (by ns_tac) as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 dropping h_v145 hinv137 s137 v145
  step as ⟨e_v147, he_v147⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s138 _ _ rfl hinv138 h64 as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 h_v146 dropping hinv138 s138
  replace h_v147 := Represents.rep_of_eq h_v147 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v147]; decide)
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo_Int.construct s139 e_v148 (by rw [he_v148]; exact empty_args) hinv139 h64 as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 h_v146 h_v147 dropping he_v147 he_v148 hinv139 e_v147 e_v148 s139
  step as ⟨e_v149, he_v149⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s140 e_v149 (by rw [he_v149]; rfl) h_v147 h_v148 hinv140 h64 as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 h_v146 dropping h_v147 h_v148 he_v149 hinv140 e_v149 s140 v147 v148
  store_step with Store.apply_rep s141 v146 v149 _ _ hinv141 h64 h_v146 h_v149 (by ns_tac) (by ns_tac) as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 dropping h_v146 h_v149 hinv141 s141 v146 v149
  step as ⟨e_v151, he_v151⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s142 _ _ rfl hinv142 h64 as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 h_v150 dropping hinv142 s142
  replace h_v151 := Represents.rep_of_eq h_v151 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v151]; decide)
  step as ⟨e_v152, he_v152⟩
  store_step with CtorSpec.eo_Int.construct s143 e_v152 (by rw [he_v152]; exact empty_args) hinv143 h64 as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 h_v150 h_v151 dropping he_v151 he_v152 hinv143 e_v151 e_v152 s143
  step as ⟨e_v153, he_v153⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s144 e_v153 (by rw [he_v153]; rfl) h_v151 h_v152 hinv144 h64 as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 h_v150 dropping h_v151 h_v152 he_v153 hinv144 e_v153 s144 v151 v152
  store_step with Store.apply_rep s145 v150 v153 _ _ hinv145 h64 h_v150 h_v153 (by ns_tac) (by ns_tac) as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 h_v144 dropping h_v150 h_v153 hinv145 s145 v150 v153
  store_step with Store.apply_rep s146 v144 v154 _ _ hinv146 h64 h_v144 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 dropping h_v144 h_v154 hinv146 s146 v144 v154
  store_step with Store.apply_rep s147 v155 v5 _ _ hinv147 h64 h_v155 h_v5 (by ns_tac) (by ns_tac) as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 h_v143 dropping h_v155 hinv147 s147 v155
  store_step with Store.apply_rep s148 v143 v156 _ _ hinv148 h64 h_v143 h_v156 (by ns_tac) (by ns_tac) as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v142 dropping h_v143 h_v156 hinv148 s148 v143 v156
  store_step with Store.apply_rep s149 v142 v157 _ _ hinv149 h64 h_v142 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 dropping h_v142 h_v157 hinv149 s149 v142 v157
  store_step with Store.literal_boolean_spec s150 false hinv150 h64 as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 h_v158 dropping hinv150 s150
  store_step with Store.apply_rep s151 v158 v159 _ _ hinv151 h64 h_v158 h_v159 (by ns_tac) (by ns_tac) as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 h_v141 dropping h_v158 h_v159 hinv151 s151 v158 v159
  store_step with Store.apply_rep s152 v141 v160 _ _ hinv152 h64 h_v141 h_v160 (by ns_tac) (by ns_tac) as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 h_v123 dropping h_v141 h_v160 hinv152 s152 v141 v160
  store_step with Store.apply_rep s153 v123 v161 _ _ hinv153 h64 h_v123 h_v161 (by ns_tac) (by ns_tac) as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 h_v112 dropping h_v123 h_v161 hinv153 s153 v123 v161
  store_step with Store.apply_rep s154 v112 v162 _ _ hinv154 h64 h_v112 h_v162 (by ns_tac) (by ns_tac) as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 h_v80 dropping h_v112 h_v162 hinv154 s154 v112 v162
  store_step with Store.apply_rep s155 v80 v163 _ _ hinv155 h64 h_v80 h_v163 (by ns_tac) (by ns_tac) as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 h_v70 dropping h_v163 h_v80 hinv155 s155 v163 v80
  store_step with Store.apply_rep s156 v70 v164 _ _ hinv156 h64 h_v70 h_v164 (by ns_tac) (by ns_tac) as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v55 dropping h_v164 h_v70 hinv156 s156 v164 v70
  store_step with Store.apply_rep s157 v55 v165 _ _ hinv157 h64 h_v55 h_v165 (by ns_tac) (by ns_tac) as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 dropping h_v165 h_v55 hinv157 s157 v165 v55
  step as ⟨e_v167, he_v167⟩
  store_step with CtorSpec.eo_and.construct s158 e_v167 (by rw [he_v167]; exact empty_args) hinv158 h64 as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 dropping he_v167 hinv158 e_v167 s158
  step as ⟨e_v168, he_v168⟩
  store_step with CtorSpec.eo_or.construct s159 e_v168 (by rw [he_v168]; exact empty_args) hinv159 h64 as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 dropping he_v168 hinv159 e_v168 s159
  step as ⟨e_v169, he_v169⟩
  store_step with CtorSpec.eo__3d.construct s160 e_v169 (by rw [he_v169]; exact empty_args) hinv160 h64 as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 dropping he_v169 hinv160 e_v169 s160
  step as ⟨e_v170, he_v170⟩
  store_step with CtorSpec.eo__40purify.construct s161 e_v170 (by rw [he_v170]; exact empty_args) hinv161 h64 as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v169 dropping he_v170 hinv161 e_v170 s161
  step as ⟨e_v171, he_v171⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s162 e_v171 (by rw [he_v171]; exact empty_args) hinv162 h64 as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v169 h_v170 dropping he_v171 hinv162 e_v171 s162
  store_step with Store.apply_rep s163 v171 v8 _ _ hinv163 h64 h_v171 h_v8 (by ns_tac) (by ns_tac) as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v169 h_v170 dropping h_v171 hinv163 s163 v171
  store_step with Store.apply_rep s164 v172 v5 _ _ hinv164 h64 h_v172 h_v5 (by ns_tac) (by ns_tac) as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v169 h_v170 dropping h_v172 hinv164 s164 v172
  store_step with Store.apply_rep s165 v173 v2 _ _ hinv165 h64 h_v173 h_v2 (by ns_tac) (by ns_tac) as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v169 h_v170 dropping h_v173 hinv165 s165 v173
  store_step with Store.apply_rep s166 v170 v174 _ _ hinv166 h64 h_v170 h_v174 (by ns_tac) (by ns_tac) as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v169 dropping h_v170 h_v174 hinv166 s166 v170 v174
  store_step with Store.apply_rep s167 v169 v175 _ _ hinv167 h64 h_v169 h_v175 (by ns_tac) (by ns_tac) as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 dropping h_v169 h_v175 hinv167 s167 v169 v175
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s168 1#u32 (-1) (by scalar_tac) hinv168 h64 as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 h_v176 dropping hinv168 s168
  store_step with Store.apply_rep s169 v176 v177 _ _ hinv169 h64 h_v176 h_v177 (by ns_tac) (by ns_tac) as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v168 dropping h_v176 h_v177 hinv169 s169 v176 v177
  store_step with Store.apply_rep s170 v168 v178 _ _ hinv170 h64 h_v168 h_v178 (by ns_tac) (by ns_tac) as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 dropping h_v168 h_v178 hinv170 s170 v168 v178
  step as ⟨e_v180, he_v180⟩
  store_step with CtorSpec.eo_or.construct s171 e_v180 (by rw [he_v180]; exact empty_args) hinv171 h64 as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 dropping he_v180 hinv171 e_v180 s171
  step as ⟨e_v181, he_v181⟩
  store_step with CtorSpec.eo_and.construct s172 e_v181 (by rw [he_v181]; exact empty_args) hinv172 h64 as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 dropping he_v181 hinv172 e_v181 s172
  step as ⟨e_v182, he_v182⟩
  store_step with CtorSpec.eo__3e_3d.construct s173 e_v182 (by rw [he_v182]; exact empty_args) hinv173 h64 as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 dropping he_v182 hinv173 e_v182 s173
  step as ⟨e_v183, he_v183⟩
  store_step with CtorSpec.eo__40purify.construct s174 e_v183 (by rw [he_v183]; exact empty_args) hinv174 h64 as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 h_v182 dropping he_v183 hinv174 e_v183 s174
  step as ⟨e_v184, he_v184⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s175 e_v184 (by rw [he_v184]; exact empty_args) hinv175 h64 as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 h_v182 h_v183 dropping he_v184 hinv175 e_v184 s175
  store_step with Store.apply_rep s176 v184 v8 _ _ hinv176 h64 h_v184 h_v8 (by ns_tac) (by ns_tac) as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 h_v182 h_v183 dropping h_v184 hinv176 s176 v184
  store_step with Store.apply_rep s177 v185 v5 _ _ hinv177 h64 h_v185 h_v5 (by ns_tac) (by ns_tac) as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 h_v182 h_v183 dropping h_v185 hinv177 s177 v185
  store_step with Store.apply_rep s178 v186 v2 _ _ hinv178 h64 h_v186 h_v2 (by ns_tac) (by ns_tac) as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 h_v182 h_v183 dropping h_v186 hinv178 s178 v186
  store_step with Store.apply_rep s179 v183 v187 _ _ hinv179 h64 h_v183 h_v187 (by ns_tac) (by ns_tac) as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 h_v182 dropping h_v183 h_v187 hinv179 s179 v183 v187
  store_step with Store.apply_rep s180 v182 v188 _ _ hinv180 h64 h_v182 h_v188 (by ns_tac) (by ns_tac) as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 dropping h_v182 h_v188 hinv180 s180 v182 v188
  store_step with Store.apply_rep s181 v189 v2 _ _ hinv181 h64 h_v189 h_v2 (by ns_tac) (by ns_tac) as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v181 dropping h_v189 hinv181 s181 v189
  store_step with Store.apply_rep s182 v181 v190 _ _ hinv182 h64 h_v181 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 dropping h_v181 h_v190 hinv182 s182 v181 v190
  step as ⟨e_v192, he_v192⟩
  store_step with CtorSpec.eo_and.construct s183 e_v192 (by rw [he_v192]; exact empty_args) hinv183 h64 as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 dropping he_v192 hinv183 e_v192 s183
  step as ⟨e_v193, he_v193⟩
  store_step with CtorSpec.eo_not.construct s184 e_v193 (by rw [he_v193]; exact empty_args) hinv184 h64 as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 dropping he_v193 hinv184 e_v193 s184
  step as ⟨e_v194, he_v194⟩
  store_step with CtorSpec.eo_forall.construct s185 e_v194 (by rw [he_v194]; exact empty_args) hinv185 h64 as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 dropping he_v194 hinv185 e_v194 s185
  step as ⟨e_v195, he_v195⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s186 e_v195 (by rw [he_v195]; exact empty_args) hinv186 h64 as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 dropping he_v195 hinv186 e_v195 s186
  step as ⟨e_v196, he_v196⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s187 _ _ rfl hinv187 h64 as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 h_v195 dropping hinv187 s187
  replace h_v196 := Represents.rep_of_eq h_v196 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v196]; decide)
  step as ⟨e_v197, he_v197⟩
  store_step with CtorSpec.eo_Int.construct s188 e_v197 (by rw [he_v197]; exact empty_args) hinv188 h64 as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 h_v195 h_v196 dropping he_v196 he_v197 hinv188 e_v196 e_v197 s188
  step as ⟨e_v198, he_v198⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s189 e_v198 (by rw [he_v198]; rfl) h_v196 h_v197 hinv189 h64 as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 h_v195 dropping h_v196 h_v197 he_v198 hinv189 e_v198 s189 v196 v197
  store_step with Store.apply_rep s190 v195 v198 _ _ hinv190 h64 h_v195 h_v198 (by ns_tac) (by ns_tac) as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 dropping h_v195 h_v198 hinv190 s190 v195 v198
  step as ⟨e_v200, he_v200⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s191 e_v200 (by rw [he_v200]; exact empty_args) hinv191 h64 as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 h_v199 dropping he_v200 hinv191 e_v200 s191
  store_step with Store.apply_rep s192 v199 v200 _ _ hinv192 h64 h_v199 h_v200 (by ns_tac) (by ns_tac) as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v194 dropping h_v199 h_v200 hinv192 s192 v199 v200
  store_step with Store.apply_rep s193 v194 v201 _ _ hinv193 h64 h_v194 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 dropping h_v194 h_v201 hinv193 s193 v194 v201
  step as ⟨e_v203, he_v203⟩
  store_step with CtorSpec.eo_or.construct s194 e_v203 (by rw [he_v203]; exact empty_args) hinv194 h64 as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 dropping he_v203 hinv194 e_v203 s194
  step as ⟨e_v204, he_v204⟩
  store_step with CtorSpec.eo_not.construct s195 e_v204 (by rw [he_v204]; exact empty_args) hinv195 h64 as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 dropping he_v204 hinv195 e_v204 s195
  step as ⟨e_v205, he_v205⟩
  store_step with CtorSpec.eo__3e_3d.construct s196 e_v205 (by rw [he_v205]; exact empty_args) hinv196 h64 as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 dropping he_v205 hinv196 e_v205 s196
  step as ⟨e_v206, he_v206⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s197 _ _ rfl hinv197 h64 as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 h_v205 dropping hinv197 s197
  replace h_v206 := Represents.rep_of_eq h_v206 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v206]; decide)
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo_Int.construct s198 e_v207 (by rw [he_v207]; exact empty_args) hinv198 h64 as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 h_v205 h_v206 dropping he_v206 he_v207 hinv198 e_v206 e_v207 s198
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s199 e_v208 (by rw [he_v208]; rfl) h_v206 h_v207 hinv199 h64 as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 h_v205 dropping h_v206 h_v207 he_v208 hinv199 e_v208 s199 v206 v207
  store_step with Store.apply_rep s200 v205 v208 _ _ hinv200 h64 h_v205 h_v208 (by ns_tac) (by ns_tac) as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 dropping h_v205 h_v208 hinv200 s200 v205 v208
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s201 0#u32 (0) (by scalar_tac) hinv201 h64 as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 h_v209 dropping hinv201 s201
  store_step with Store.apply_rep s202 v209 v210 _ _ hinv202 h64 h_v209 h_v210 (by ns_tac) (by ns_tac) as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 h_v204 dropping h_v209 h_v210 hinv202 s202 v209 v210
  store_step with Store.apply_rep s203 v204 v211 _ _ hinv203 h64 h_v204 h_v211 (by ns_tac) (by ns_tac) as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v203 dropping h_v204 h_v211 hinv203 s203 v204 v211
  store_step with Store.apply_rep s204 v203 v212 _ _ hinv204 h64 h_v203 h_v212 (by ns_tac) (by ns_tac) as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 dropping h_v203 h_v212 hinv204 s204 v203 v212
  step as ⟨e_v214, he_v214⟩
  store_step with CtorSpec.eo_or.construct s205 e_v214 (by rw [he_v214]; exact empty_args) hinv205 h64 as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 dropping he_v214 hinv205 e_v214 s205
  step as ⟨e_v215, he_v215⟩
  store_step with CtorSpec.eo_not.construct s206 e_v215 (by rw [he_v215]; exact empty_args) hinv206 h64 as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 dropping he_v215 hinv206 e_v215 s206
  step as ⟨e_v216, he_v216⟩
  store_step with CtorSpec.eo__3c_3d.construct s207 e_v216 (by rw [he_v216]; exact empty_args) hinv207 h64 as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 dropping he_v216 hinv207 e_v216 s207
  step as ⟨e_v217, he_v217⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s208 _ _ rfl hinv208 h64 as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v216 dropping hinv208 s208
  replace h_v217 := Represents.rep_of_eq h_v217 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v217]; decide)
  step as ⟨e_v218, he_v218⟩
  store_step with CtorSpec.eo_Int.construct s209 e_v218 (by rw [he_v218]; exact empty_args) hinv209 h64 as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v216 h_v217 dropping he_v217 he_v218 hinv209 e_v217 e_v218 s209
  step as ⟨e_v219, he_v219⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s210 e_v219 (by rw [he_v219]; rfl) h_v217 h_v218 hinv210 h64 as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v216 dropping h_v217 h_v218 he_v219 hinv210 e_v219 s210 v217 v218
  store_step with Store.apply_rep s211 v216 v219 _ _ hinv211 h64 h_v216 h_v219 (by ns_tac) (by ns_tac) as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 dropping h_v216 h_v219 hinv211 s211 v216 v219
  step as ⟨e_v221, he_v221⟩
  store_step with CtorSpec.eo__2d.construct s212 e_v221 (by rw [he_v221]; exact empty_args) hinv212 h64 as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 dropping he_v221 hinv212 e_v221 s212
  step as ⟨e_v222, he_v222⟩
  store_step with CtorSpec.eo_str_2elen.construct s213 e_v222 (by rw [he_v222]; exact empty_args) hinv213 h64 as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v221 dropping he_v222 hinv213 e_v222 s213
  store_step with Store.apply_rep s214 v222 v8 _ _ hinv214 h64 h_v222 h_v8 (by ns_tac) (by ns_tac) as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v221 dropping h_v222 hinv214 s214 v222
  store_step with Store.apply_rep s215 v221 v223 _ _ hinv215 h64 h_v221 h_v223 (by ns_tac) (by ns_tac) as ⟨v224, s216, hinv216, h_v224⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 dropping h_v221 h_v223 hinv215 s215 v221 v223
  step as ⟨e_v225, he_v225⟩
  store_step with CtorSpec.eo__40purify.construct s216 e_v225 (by rw [he_v225]; exact empty_args) hinv216 h64 as ⟨v225, s217, hinv217, h_v225⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v224 dropping he_v225 hinv216 e_v225 s216
  step as ⟨e_v226, he_v226⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s217 e_v226 (by rw [he_v226]; exact empty_args) hinv217 h64 as ⟨v226, s218, hinv218, h_v226⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v224 h_v225 dropping he_v226 hinv217 e_v226 s217
  store_step with Store.apply_rep s218 v226 v8 _ _ hinv218 h64 h_v226 h_v8 (by ns_tac) (by ns_tac) as ⟨v227, s219, hinv219, h_v227⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v224 h_v225 dropping h_v226 hinv218 s218 v226
  store_step with Store.apply_rep s219 v227 v5 _ _ hinv219 h64 h_v227 h_v5 (by ns_tac) (by ns_tac) as ⟨v228, s220, hinv220, h_v228⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v224 h_v225 dropping h_v227 hinv219 s219 v227
  store_step with Store.apply_rep s220 v228 v2 _ _ hinv220 h64 h_v228 h_v2 (by ns_tac) (by ns_tac) as ⟨v229, s221, hinv221, h_v229⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v224 h_v225 dropping h_v228 hinv220 s220 v228
  store_step with Store.apply_rep s221 v225 v229 _ _ hinv221 h64 h_v225 h_v229 (by ns_tac) (by ns_tac) as ⟨v230, s222, hinv222, h_v230⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 h_v224 dropping h_v225 h_v229 hinv221 s221 v225 v229
  store_step with Store.apply_rep s222 v224 v230 _ _ hinv222 h64 h_v224 h_v230 (by ns_tac) (by ns_tac) as ⟨v231, s223, hinv223, h_v231⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 h_v220 dropping h_v224 h_v230 hinv222 s222 v224 v230
  store_step with Store.apply_rep s223 v220 v231 _ _ hinv223 h64 h_v220 h_v231 (by ns_tac) (by ns_tac) as ⟨v232, s224, hinv224, h_v232⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 h_v215 dropping h_v220 h_v231 hinv223 s223 v220 v231
  store_step with Store.apply_rep s224 v215 v232 _ _ hinv224 h64 h_v215 h_v232 (by ns_tac) (by ns_tac) as ⟨v233, s225, hinv225, h_v233⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v214 dropping h_v215 h_v232 hinv224 s224 v215 v232
  store_step with Store.apply_rep s225 v214 v233 _ _ hinv225 h64 h_v214 h_v233 (by ns_tac) (by ns_tac) as ⟨v234, s226, hinv226, h_v234⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 dropping h_v214 h_v233 hinv225 s225 v214 v233
  step as ⟨e_v235, he_v235⟩
  store_step with CtorSpec.eo_or.construct s226 e_v235 (by rw [he_v235]; exact empty_args) hinv226 h64 as ⟨v235, s227, hinv227, h_v235⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 dropping he_v235 hinv226 e_v235 s226
  step as ⟨e_v236, he_v236⟩
  store_step with CtorSpec.eo_not.construct s227 e_v236 (by rw [he_v236]; exact empty_args) hinv227 h64 as ⟨v236, s228, hinv228, h_v236⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 dropping he_v236 hinv227 e_v236 s227
  step as ⟨e_v237, he_v237⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s228 e_v237 (by rw [he_v237]; exact empty_args) hinv228 h64 as ⟨v237, s229, hinv229, h_v237⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 dropping he_v237 hinv228 e_v237 s228
  step as ⟨e_v238, he_v238⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s229 e_v238 (by rw [he_v238]; exact empty_args) hinv229 h64 as ⟨v238, s230, hinv230, h_v238⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 dropping he_v238 hinv229 e_v238 s229
  store_step with Store.apply_rep s230 v238 v8 _ _ hinv230 h64 h_v238 h_v8 (by ns_tac) (by ns_tac) as ⟨v239, s231, hinv231, h_v239⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 dropping h_v238 hinv230 s230 v238
  step as ⟨e_v240, he_v240⟩
  store_step with CtorSpec.eo__40purify.construct s231 e_v240 (by rw [he_v240]; exact empty_args) hinv231 h64 as ⟨v240, s232, hinv232, h_v240⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v239 dropping he_v240 hinv231 e_v240 s231
  step as ⟨e_v241, he_v241⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s232 e_v241 (by rw [he_v241]; exact empty_args) hinv232 h64 as ⟨v241, s233, hinv233, h_v241⟩ growing hG carrying h_v2 h_v5 h_v8 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v239 h_v240 dropping he_v241 hinv232 e_v241 s232
  store_step with Store.apply_rep s233 v241 v8 _ _ hinv233 h64 h_v241 h_v8 (by ns_tac) (by ns_tac) as ⟨v242, s234, hinv234, h_v242⟩ growing hG carrying h_v2 h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v239 h_v240 dropping h_v241 h_v8 hinv233 s233 v241 v8
  store_step with Store.apply_rep s234 v242 v5 _ _ hinv234 h64 h_v242 h_v5 (by ns_tac) (by ns_tac) as ⟨v243, s235, hinv235, h_v243⟩ growing hG carrying h_v2 h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v239 h_v240 dropping h_v242 hinv234 s234 v242
  store_step with Store.apply_rep s235 v243 v2 _ _ hinv235 h64 h_v243 h_v2 (by ns_tac) (by ns_tac) as ⟨v244, s236, hinv236, h_v244⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v239 h_v240 dropping h_v2 h_v243 hinv235 s235 v2 v243
  store_step with Store.apply_rep s236 v240 v244 _ _ hinv236 h64 h_v240 h_v244 (by ns_tac) (by ns_tac) as ⟨v245, s237, hinv237, h_v245⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v239 dropping h_v240 h_v244 hinv236 s236 v240 v244
  store_step with Store.apply_rep s237 v239 v245 _ _ hinv237 h64 h_v239 h_v245 (by ns_tac) (by ns_tac) as ⟨v246, s238, hinv238, h_v246⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 dropping h_v239 h_v245 hinv237 s237 v239 v245
  step as ⟨e_v247, he_v247⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s238 _ _ rfl hinv238 h64 as ⟨v247, s239, hinv239, h_v247⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v246 dropping hinv238 s238
  replace h_v247 := Represents.rep_of_eq h_v247 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v247]; decide)
  step as ⟨e_v248, he_v248⟩
  store_step with CtorSpec.eo_Int.construct s239 e_v248 (by rw [he_v248]; exact empty_args) hinv239 h64 as ⟨v248, s240, hinv240, h_v248⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v246 h_v247 dropping he_v247 he_v248 hinv239 e_v247 e_v248 s239
  step as ⟨e_v249, he_v249⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s240 e_v249 (by rw [he_v249]; rfl) h_v247 h_v248 hinv240 h64 as ⟨v249, s241, hinv241, h_v249⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 h_v246 dropping h_v247 h_v248 he_v249 hinv240 e_v249 s240 v247 v248
  store_step with Store.apply_rep s241 v246 v249 _ _ hinv241 h64 h_v246 h_v249 (by ns_tac) (by ns_tac) as ⟨v250, s242, hinv242, h_v250⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 h_v237 dropping h_v246 h_v249 hinv241 s241 v246 v249
  store_step with Store.apply_rep s242 v237 v250 _ _ hinv242 h64 h_v237 h_v250 (by ns_tac) (by ns_tac) as ⟨v251, s243, hinv243, h_v251⟩ growing hG carrying h_v5 h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 dropping h_v237 h_v250 hinv242 s242 v237 v250
  store_step with Store.apply_rep s243 v251 v5 _ _ hinv243 h64 h_v251 h_v5 (by ns_tac) (by ns_tac) as ⟨v252, s244, hinv244, h_v252⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 h_v236 dropping h_v251 h_v5 hinv243 s243 v251 v5
  store_step with Store.apply_rep s244 v236 v252 _ _ hinv244 h64 h_v236 h_v252 (by ns_tac) (by ns_tac) as ⟨v253, s245, hinv245, h_v253⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v235 dropping h_v236 h_v252 hinv244 s244 v236 v252
  store_step with Store.apply_rep s245 v235 v253 _ _ hinv245 h64 h_v235 h_v253 (by ns_tac) (by ns_tac) as ⟨v254, s246, hinv246, h_v254⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 dropping h_v235 h_v253 hinv245 s245 v235 v253
  store_step with Store.literal_boolean_spec s246 false hinv246 h64 as ⟨v255, s247, hinv247, h_v255⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 h_v254 dropping hinv246 s246
  store_step with Store.apply_rep s247 v254 v255 _ _ hinv247 h64 h_v254 h_v255 (by ns_tac) (by ns_tac) as ⟨v256, s248, hinv248, h_v256⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 h_v234 dropping h_v254 h_v255 hinv247 s247 v254 v255
  store_step with Store.apply_rep s248 v234 v256 _ _ hinv248 h64 h_v234 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s249, hinv249, h_v257⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 h_v213 dropping h_v234 h_v256 hinv248 s248 v234 v256
  store_step with Store.apply_rep s249 v213 v257 _ _ hinv249 h64 h_v213 h_v257 (by ns_tac) (by ns_tac) as ⟨v258, s250, hinv250, h_v258⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 h_v202 dropping h_v213 h_v257 hinv249 s249 v213 v257
  store_step with Store.apply_rep s250 v202 v258 _ _ hinv250 h64 h_v202 h_v258 (by ns_tac) (by ns_tac) as ⟨v259, s251, hinv251, h_v259⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 h_v193 dropping h_v202 h_v258 hinv250 s250 v202 v258
  store_step with Store.apply_rep s251 v193 v259 _ _ hinv251 h64 h_v193 h_v259 (by ns_tac) (by ns_tac) as ⟨v260, s252, hinv252, h_v260⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v192 dropping h_v193 h_v259 hinv251 s251 v193 v259
  store_step with Store.apply_rep s252 v192 v260 _ _ hinv252 h64 h_v192 h_v260 (by ns_tac) (by ns_tac) as ⟨v261, s253, hinv253, h_v261⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 dropping h_v192 h_v260 hinv252 s252 v192 v260
  store_step with Store.literal_boolean_spec s253 true hinv253 h64 as ⟨v262, s254, hinv254, h_v262⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 h_v261 dropping hinv253 s253
  store_step with Store.apply_rep s254 v261 v262 _ _ hinv254 h64 h_v261 h_v262 (by ns_tac) (by ns_tac) as ⟨v263, s255, hinv255, h_v263⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 h_v191 dropping h_v261 h_v262 hinv254 s254 v261 v262
  store_step with Store.apply_rep s255 v191 v263 _ _ hinv255 h64 h_v191 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s256, hinv256, h_v264⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v180 dropping h_v191 h_v263 hinv255 s255 v191 v263
  store_step with Store.apply_rep s256 v180 v264 _ _ hinv256 h64 h_v180 h_v264 (by ns_tac) (by ns_tac) as ⟨v265, s257, hinv257, h_v265⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 dropping h_v180 h_v264 hinv256 s256 v180 v264
  store_step with Store.literal_boolean_spec s257 false hinv257 h64 as ⟨v266, s258, hinv258, h_v266⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 h_v265 dropping hinv257 s257
  store_step with Store.apply_rep s258 v265 v266 _ _ hinv258 h64 h_v265 h_v266 (by ns_tac) (by ns_tac) as ⟨v267, s259, hinv259, h_v267⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 h_v179 dropping h_v265 h_v266 hinv258 s258 v265 v266
  store_step with Store.apply_rep s259 v179 v267 _ _ hinv259 h64 h_v179 h_v267 (by ns_tac) (by ns_tac) as ⟨v268, s260, hinv260, h_v268⟩ growing hG carrying h_v38 h_v54 h_v166 h_v167 dropping h_v179 h_v267 hinv259 s259 v179 v267
  store_step with Store.apply_rep s260 v167 v268 _ _ hinv260 h64 h_v167 h_v268 (by ns_tac) (by ns_tac) as ⟨v269, s261, hinv261, h_v269⟩ growing hG carrying h_v38 h_v54 h_v166 dropping h_v167 h_v268 hinv260 s260 v167 v268
  store_step with Store.literal_boolean_spec s261 true hinv261 h64 as ⟨v270, s262, hinv262, h_v270⟩ growing hG carrying h_v38 h_v54 h_v166 h_v269 dropping hinv261 s261
  store_step with Store.apply_rep s262 v269 v270 _ _ hinv262 h64 h_v269 h_v270 (by ns_tac) (by ns_tac) as ⟨v271, s263, hinv263, h_v271⟩ growing hG carrying h_v38 h_v54 h_v166 dropping h_v269 h_v270 hinv262 s262 v269 v270
  store_step with Store.apply_rep s263 v166 v271 _ _ hinv263 h64 h_v166 h_v271 (by ns_tac) (by ns_tac) as ⟨v272, s264, hinv264, h_v272⟩ growing hG carrying h_v38 h_v54 dropping h_v166 h_v271 hinv263 s263 v166 v271
  store_step with Store.apply_rep s264 v54 v272 _ _ hinv264 h64 h_v54 h_v272 (by ns_tac) (by ns_tac) as ⟨v273, s265, hinv265, h_v273⟩ growing hG carrying h_v38 dropping h_v272 h_v54 hinv264 s264 v272 v54
  store_step with Store.apply_rep s265 v38 v273 _ _ hinv265 h64 h_v38 h_v273 (by ns_tac) (by ns_tac) as ⟨v274, s266, hinv266, h_v274⟩ growing hG carrying dropping h_v273 h_v38 hinv265 s265 v273 v38
  case_done hinv266 hG with h_v274 in EoCases.__str_reduction_pred.case_11 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

set_option maxHeartbeats 4380000 in
theorem case_12_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_12_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_12 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_12 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_12
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_12
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2e_3c_3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_12
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40purify.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_str_2e_3c_3d.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v5 _ _ hinv8 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v13 hinv8 s8 v13
  store_step with Store.apply_rep s9 v14 v2 _ _ hinv9 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v14 hinv9 s9 v14
  store_step with Store.apply_rep s10 v12 v15 _ _ hinv10 h64 h_v12 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v12 h_v15 hinv10 s10 v12 v15
  store_step with Store.apply_rep s11 v11 v16 _ _ hinv11 h64 h_v11 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 dropping h_v11 h_v16 hinv11 s11 v11 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_not.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v17 dropping he_v18 hinv12 e_v18 s12
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_forall.construct s13 e_v19 (by rw [he_v19]; exact empty_args) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 dropping he_v19 hinv13 e_v19 s13
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 dropping he_v20 hinv14 e_v20 s14
  step as ⟨e_v21, he_v21⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s15 _ _ rfl hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 h_v20 dropping hinv15 s15
  replace h_v21 := Represents.rep_of_eq h_v21 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v21]; decide)
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_Int.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 h_v20 h_v21 dropping he_v21 he_v22 hinv16 e_v21 e_v22 s16
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s17 e_v23 (by rw [he_v23]; rfl) h_v21 h_v22 hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 h_v20 dropping h_v21 h_v22 he_v23 hinv17 e_v23 s17 v21 v22
  store_step with Store.apply_rep s18 v20 v23 _ _ hinv18 h64 h_v20 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 dropping h_v20 h_v23 hinv18 s18 v20 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 h_v24 dropping he_v25 hinv19 e_v25 s19
  store_step with Store.apply_rep s20 v24 v25 _ _ hinv20 h64 h_v24 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v19 dropping h_v24 h_v25 hinv20 s20 v24 v25
  store_step with Store.apply_rep s21 v19 v26 _ _ hinv21 h64 h_v19 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 dropping h_v19 h_v26 hinv21 s21 v19 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_or.construct s22 e_v28 (by rw [he_v28]; exact empty_args) hinv22 h64 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 dropping he_v28 hinv22 e_v28 s22
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_not.construct s23 e_v29 (by rw [he_v29]; exact empty_args) hinv23 h64 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 dropping he_v29 hinv23 e_v29 s23
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3e_3d.construct s24 e_v30 (by rw [he_v30]; exact empty_args) hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 dropping he_v30 hinv24 e_v30 s24
  step as ⟨e_v31, he_v31⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s25 _ _ rfl hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 h_v30 dropping hinv25 s25
  replace h_v31 := Represents.rep_of_eq h_v31 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v31]; decide)
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_Int.construct s26 e_v32 (by rw [he_v32]; exact empty_args) hinv26 h64 as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 h_v30 h_v31 dropping he_v31 he_v32 hinv26 e_v31 e_v32 s26
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s27 e_v33 (by rw [he_v33]; rfl) h_v31 h_v32 hinv27 h64 as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 h_v30 dropping h_v31 h_v32 he_v33 hinv27 e_v33 s27 v31 v32
  store_step with Store.apply_rep s28 v30 v33 _ _ hinv28 h64 h_v30 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 dropping h_v30 h_v33 hinv28 s28 v30 v33
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 0#u32 (0) (by scalar_tac) hinv29 h64 as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 h_v34 dropping hinv29 s29
  store_step with Store.apply_rep s30 v34 v35 _ _ hinv30 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 h_v29 dropping h_v34 h_v35 hinv30 s30 v34 v35
  store_step with Store.apply_rep s31 v29 v36 _ _ hinv31 h64 h_v29 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v28 dropping h_v29 h_v36 hinv31 s31 v29 v36
  store_step with Store.apply_rep s32 v28 v37 _ _ hinv32 h64 h_v28 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 dropping h_v28 h_v37 hinv32 s32 v28 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_or.construct s33 e_v39 (by rw [he_v39]; exact empty_args) hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 dropping he_v39 hinv33 e_v39 s33
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_not.construct s34 e_v40 (by rw [he_v40]; exact empty_args) hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 dropping he_v40 hinv34 e_v40 s34
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3c_3d.construct s35 e_v41 (by rw [he_v41]; exact empty_args) hinv35 h64 as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 dropping he_v41 hinv35 e_v41 s35
  step as ⟨e_v42, he_v42⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s36 _ _ rfl hinv36 h64 as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 h_v41 dropping hinv36 s36
  replace h_v42 := Represents.rep_of_eq h_v42 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v42]; decide)
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_Int.construct s37 e_v43 (by rw [he_v43]; exact empty_args) hinv37 h64 as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 h_v41 h_v42 dropping he_v42 he_v43 hinv37 e_v42 e_v43 s37
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s38 e_v44 (by rw [he_v44]; rfl) h_v42 h_v43 hinv38 h64 as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 h_v41 dropping h_v42 h_v43 he_v44 hinv38 e_v44 s38 v42 v43
  store_step with Store.apply_rep s39 v41 v44 _ _ hinv39 h64 h_v41 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 dropping h_v41 h_v44 hinv39 s39 v41 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2elen.construct s40 e_v46 (by rw [he_v46]; exact empty_args) hinv40 h64 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 h_v45 dropping he_v46 hinv40 e_v46 s40
  store_step with Store.apply_rep s41 v46 v5 _ _ hinv41 h64 h_v46 h_v5 (by ns_tac) (by ns_tac) as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 h_v45 dropping h_v46 hinv41 s41 v46
  store_step with Store.apply_rep s42 v45 v47 _ _ hinv42 h64 h_v45 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 h_v40 dropping h_v45 h_v47 hinv42 s42 v45 v47
  store_step with Store.apply_rep s43 v40 v48 _ _ hinv43 h64 h_v40 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v39 dropping h_v40 h_v48 hinv43 s43 v40 v48
  store_step with Store.apply_rep s44 v39 v49 _ _ hinv44 h64 h_v39 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 dropping h_v39 h_v49 hinv44 s44 v39 v49
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_or.construct s45 e_v51 (by rw [he_v51]; exact empty_args) hinv45 h64 as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 dropping he_v51 hinv45 e_v51 s45
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo_not.construct s46 e_v52 (by rw [he_v52]; exact empty_args) hinv46 h64 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 dropping he_v52 hinv46 e_v52 s46
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo__3c_3d.construct s47 e_v53 (by rw [he_v53]; exact empty_args) hinv47 h64 as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 dropping he_v53 hinv47 e_v53 s47
  step as ⟨e_v54, he_v54⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s48 _ _ rfl hinv48 h64 as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 h_v53 dropping hinv48 s48
  replace h_v54 := Represents.rep_of_eq h_v54 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v54]; decide)
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_Int.construct s49 e_v55 (by rw [he_v55]; exact empty_args) hinv49 h64 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 h_v53 h_v54 dropping he_v54 he_v55 hinv49 e_v54 e_v55 s49
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s50 e_v56 (by rw [he_v56]; rfl) h_v54 h_v55 hinv50 h64 as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 h_v53 dropping h_v54 h_v55 he_v56 hinv50 e_v56 s50 v54 v55
  store_step with Store.apply_rep s51 v53 v56 _ _ hinv51 h64 h_v53 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 dropping h_v53 h_v56 hinv51 s51 v53 v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_str_2elen.construct s52 e_v58 (by rw [he_v58]; exact empty_args) hinv52 h64 as ⟨v58, s53, hinv53, h_v58⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 h_v57 dropping he_v58 hinv52 e_v58 s52
  store_step with Store.apply_rep s53 v58 v2 _ _ hinv53 h64 h_v58 h_v2 (by ns_tac) (by ns_tac) as ⟨v59, s54, hinv54, h_v59⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 h_v57 dropping h_v58 hinv53 s53 v58
  store_step with Store.apply_rep s54 v57 v59 _ _ hinv54 h64 h_v57 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s55, hinv55, h_v60⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 h_v52 dropping h_v57 h_v59 hinv54 s54 v57 v59
  store_step with Store.apply_rep s55 v52 v60 _ _ hinv55 h64 h_v52 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s56, hinv56, h_v61⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v51 dropping h_v52 h_v60 hinv55 s55 v52 v60
  store_step with Store.apply_rep s56 v51 v61 _ _ hinv56 h64 h_v51 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s57, hinv57, h_v62⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 dropping h_v51 h_v61 hinv56 s56 v51 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_or.construct s57 e_v63 (by rw [he_v63]; exact empty_args) hinv57 h64 as ⟨v63, s58, hinv58, h_v63⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 dropping he_v63 hinv57 e_v63 s57
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_not.construct s58 e_v64 (by rw [he_v64]; exact empty_args) hinv58 h64 as ⟨v64, s59, hinv59, h_v64⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 dropping he_v64 hinv58 e_v64 s58
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__3d.construct s59 e_v65 (by rw [he_v65]; exact empty_args) hinv59 h64 as ⟨v65, s60, hinv60, h_v65⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 dropping he_v65 hinv59 e_v65 s59
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s60 e_v66 (by rw [he_v66]; exact empty_args) hinv60 h64 as ⟨v66, s61, hinv61, h_v66⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 dropping he_v66 hinv60 e_v66 s60
  store_step with Store.apply_rep s61 v66 v5 _ _ hinv61 h64 h_v66 h_v5 (by ns_tac) (by ns_tac) as ⟨v67, s62, hinv62, h_v67⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 dropping h_v66 hinv61 s61 v66
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s62 0#u32 (0) (by scalar_tac) hinv62 h64 as ⟨v68, s63, hinv63, h_v68⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 h_v67 dropping hinv62 s62
  store_step with Store.apply_rep s63 v67 v68 _ _ hinv63 h64 h_v67 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s64, hinv64, h_v69⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 dropping h_v67 h_v68 hinv63 s63 v67 v68
  step as ⟨e_v70, he_v70⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s64 _ _ rfl hinv64 h64 as ⟨v70, s65, hinv65, h_v70⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 h_v69 dropping hinv64 s64
  replace h_v70 := Represents.rep_of_eq h_v70 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v70]; decide)
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_Int.construct s65 e_v71 (by rw [he_v71]; exact empty_args) hinv65 h64 as ⟨v71, s66, hinv66, h_v71⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 h_v69 h_v70 dropping he_v70 he_v71 hinv65 e_v70 e_v71 s65
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s66 e_v72 (by rw [he_v72]; rfl) h_v70 h_v71 hinv66 h64 as ⟨v72, s67, hinv67, h_v72⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 h_v69 dropping h_v70 h_v71 he_v72 hinv66 e_v72 s66 v70 v71
  store_step with Store.apply_rep s67 v69 v72 _ _ hinv67 h64 h_v69 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s68, hinv68, h_v73⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v65 dropping h_v69 h_v72 hinv67 s67 v69 v72
  store_step with Store.apply_rep s68 v65 v73 _ _ hinv68 h64 h_v65 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s69, hinv69, h_v74⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 dropping h_v65 h_v73 hinv68 s68 v65 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s69 e_v75 (by rw [he_v75]; exact empty_args) hinv69 h64 as ⟨v75, s70, hinv70, h_v75⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 dropping he_v75 hinv69 e_v75 s69
  store_step with Store.apply_rep s70 v75 v2 _ _ hinv70 h64 h_v75 h_v2 (by ns_tac) (by ns_tac) as ⟨v76, s71, hinv71, h_v76⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 dropping h_v75 hinv70 s70 v75
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s71 0#u32 (0) (by scalar_tac) hinv71 h64 as ⟨v77, s72, hinv72, h_v77⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 h_v76 dropping hinv71 s71
  store_step with Store.apply_rep s72 v76 v77 _ _ hinv72 h64 h_v76 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s73, hinv73, h_v78⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 dropping h_v76 h_v77 hinv72 s72 v76 v77
  step as ⟨e_v79, he_v79⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s73 _ _ rfl hinv73 h64 as ⟨v79, s74, hinv74, h_v79⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 h_v78 dropping hinv73 s73
  replace h_v79 := Represents.rep_of_eq h_v79 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v79]; decide)
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_Int.construct s74 e_v80 (by rw [he_v80]; exact empty_args) hinv74 h64 as ⟨v80, s75, hinv75, h_v80⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 h_v78 h_v79 dropping he_v79 he_v80 hinv74 e_v79 e_v80 s74
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s75 e_v81 (by rw [he_v81]; rfl) h_v79 h_v80 hinv75 h64 as ⟨v81, s76, hinv76, h_v81⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 h_v78 dropping h_v79 h_v80 he_v81 hinv75 e_v81 s75 v79 v80
  store_step with Store.apply_rep s76 v78 v81 _ _ hinv76 h64 h_v78 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s77, hinv77, h_v82⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 h_v74 dropping h_v78 h_v81 hinv76 s76 v78 v81
  store_step with Store.apply_rep s77 v74 v82 _ _ hinv77 h64 h_v74 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s78, hinv78, h_v83⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 h_v64 dropping h_v74 h_v82 hinv77 s77 v74 v82
  store_step with Store.apply_rep s78 v64 v83 _ _ hinv78 h64 h_v64 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s79, hinv79, h_v84⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v63 dropping h_v64 h_v83 hinv78 s78 v64 v83
  store_step with Store.apply_rep s79 v63 v84 _ _ hinv79 h64 h_v63 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s80, hinv80, h_v85⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 dropping h_v63 h_v84 hinv79 s79 v63 v84
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_or.construct s80 e_v86 (by rw [he_v86]; exact empty_args) hinv80 h64 as ⟨v86, s81, hinv81, h_v86⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 dropping he_v86 hinv80 e_v86 s80
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo_ite.construct s81 e_v87 (by rw [he_v87]; exact empty_args) hinv81 h64 as ⟨v87, s82, hinv82, h_v87⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 dropping he_v87 hinv81 e_v87 s81
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo__40purify.construct s82 e_v88 (by rw [he_v88]; exact empty_args) hinv82 h64 as ⟨v88, s83, hinv83, h_v88⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v87 dropping he_v88 hinv82 e_v88 s82
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo_str_2e_3c_3d.construct s83 e_v89 (by rw [he_v89]; exact empty_args) hinv83 h64 as ⟨v89, s84, hinv84, h_v89⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v87 h_v88 dropping he_v89 hinv83 e_v89 s83
  store_step with Store.apply_rep s84 v89 v5 _ _ hinv84 h64 h_v89 h_v5 (by ns_tac) (by ns_tac) as ⟨v90, s85, hinv85, h_v90⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v87 h_v88 dropping h_v89 hinv84 s84 v89
  store_step with Store.apply_rep s85 v90 v2 _ _ hinv85 h64 h_v90 h_v2 (by ns_tac) (by ns_tac) as ⟨v91, s86, hinv86, h_v91⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v87 h_v88 dropping h_v90 hinv85 s85 v90
  store_step with Store.apply_rep s86 v88 v91 _ _ hinv86 h64 h_v88 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s87, hinv87, h_v92⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v87 dropping h_v88 h_v91 hinv86 s86 v88 v91
  store_step with Store.apply_rep s87 v87 v92 _ _ hinv87 h64 h_v87 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s88, hinv88, h_v93⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 dropping h_v87 h_v92 hinv87 s87 v87 v92
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo__3e_3d.construct s88 e_v94 (by rw [he_v94]; exact empty_args) hinv88 h64 as ⟨v94, s89, hinv89, h_v94⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 dropping he_v94 hinv88 e_v94 s88
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s89 e_v95 (by rw [he_v95]; exact empty_args) hinv89 h64 as ⟨v95, s90, hinv90, h_v95⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 dropping he_v95 hinv89 e_v95 s89
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s90 e_v96 (by rw [he_v96]; exact empty_args) hinv90 h64 as ⟨v96, s91, hinv91, h_v96⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 dropping he_v96 hinv90 e_v96 s90
  store_step with Store.apply_rep s91 v96 v5 _ _ hinv91 h64 h_v96 h_v5 (by ns_tac) (by ns_tac) as ⟨v97, s92, hinv92, h_v97⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 dropping h_v96 hinv91 s91 v96
  step as ⟨e_v98, he_v98⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s92 _ _ rfl hinv92 h64 as ⟨v98, s93, hinv93, h_v98⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 h_v97 dropping hinv92 s92
  replace h_v98 := Represents.rep_of_eq h_v98 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v98]; decide)
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_Int.construct s93 e_v99 (by rw [he_v99]; exact empty_args) hinv93 h64 as ⟨v99, s94, hinv94, h_v99⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 h_v97 h_v98 dropping he_v98 he_v99 hinv93 e_v98 e_v99 s93
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s94 e_v100 (by rw [he_v100]; rfl) h_v98 h_v99 hinv94 h64 as ⟨v100, s95, hinv95, h_v100⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 h_v97 dropping h_v98 h_v99 he_v100 hinv94 e_v100 s94 v98 v99
  store_step with Store.apply_rep s95 v97 v100 _ _ hinv95 h64 h_v97 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s96, hinv96, h_v101⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 dropping h_v100 h_v97 hinv95 s95 v100 v97
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s96 1#u32 (1) (by scalar_tac) hinv96 h64 as ⟨v102, s97, hinv97, h_v102⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 h_v101 dropping hinv96 s96
  store_step with Store.apply_rep s97 v101 v102 _ _ hinv97 h64 h_v101 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s98, hinv98, h_v103⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 h_v95 dropping h_v101 h_v102 hinv97 s97 v101 v102
  store_step with Store.apply_rep s98 v95 v103 _ _ hinv98 h64 h_v95 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s99, hinv99, h_v104⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v94 dropping h_v103 h_v95 hinv98 s98 v103 v95
  store_step with Store.apply_rep s99 v94 v104 _ _ hinv99 h64 h_v94 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s100, hinv100, h_v105⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 dropping h_v104 h_v94 hinv99 s99 v104 v94
  step as ⟨e_v106, he_v106⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s100 e_v106 (by rw [he_v106]; exact empty_args) hinv100 h64 as ⟨v106, s101, hinv101, h_v106⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 dropping he_v106 hinv100 e_v106 s100
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s101 e_v107 (by rw [he_v107]; exact empty_args) hinv101 h64 as ⟨v107, s102, hinv102, h_v107⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 dropping he_v107 hinv101 e_v107 s101
  store_step with Store.apply_rep s102 v107 v2 _ _ hinv102 h64 h_v107 h_v2 (by ns_tac) (by ns_tac) as ⟨v108, s103, hinv103, h_v108⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 dropping h_v107 hinv102 s102 v107
  step as ⟨e_v109, he_v109⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s103 _ _ rfl hinv103 h64 as ⟨v109, s104, hinv104, h_v109⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 h_v108 dropping hinv103 s103
  replace h_v109 := Represents.rep_of_eq h_v109 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v109]; decide)
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo_Int.construct s104 e_v110 (by rw [he_v110]; exact empty_args) hinv104 h64 as ⟨v110, s105, hinv105, h_v110⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 h_v108 h_v109 dropping he_v109 he_v110 hinv104 e_v109 e_v110 s104
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s105 e_v111 (by rw [he_v111]; rfl) h_v109 h_v110 hinv105 h64 as ⟨v111, s106, hinv106, h_v111⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 h_v108 dropping h_v109 h_v110 he_v111 hinv105 e_v111 s105 v109 v110
  store_step with Store.apply_rep s106 v108 v111 _ _ hinv106 h64 h_v108 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s107, hinv107, h_v112⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 dropping h_v108 h_v111 hinv106 s106 v108 v111
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s107 1#u32 (1) (by scalar_tac) hinv107 h64 as ⟨v113, s108, hinv108, h_v113⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 h_v112 dropping hinv107 s107
  store_step with Store.apply_rep s108 v112 v113 _ _ hinv108 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s109, hinv109, h_v114⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 h_v106 dropping h_v112 h_v113 hinv108 s108 v112 v113
  store_step with Store.apply_rep s109 v106 v114 _ _ hinv109 h64 h_v106 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s110, hinv110, h_v115⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 h_v105 dropping h_v106 h_v114 hinv109 s109 v106 v114
  store_step with Store.apply_rep s110 v105 v115 _ _ hinv110 h64 h_v105 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s111, hinv111, h_v116⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v93 dropping h_v105 h_v115 hinv110 s110 v105 v115
  store_step with Store.apply_rep s111 v93 v116 _ _ hinv111 h64 h_v93 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s112, hinv112, h_v117⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 dropping h_v116 h_v93 hinv111 s111 v116 v93
  step as ⟨e_v118, he_v118⟩
  store_step with CtorSpec.eo__3e_3d.construct s112 e_v118 (by rw [he_v118]; exact empty_args) hinv112 h64 as ⟨v118, s113, hinv113, h_v118⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 dropping he_v118 hinv112 e_v118 s112
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s113 e_v119 (by rw [he_v119]; exact empty_args) hinv113 h64 as ⟨v119, s114, hinv114, h_v119⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 dropping he_v119 hinv113 e_v119 s113
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s114 e_v120 (by rw [he_v120]; exact empty_args) hinv114 h64 as ⟨v120, s115, hinv115, h_v120⟩ growing hG carrying h_v2 h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 dropping he_v120 hinv114 e_v120 s114
  store_step with Store.apply_rep s115 v120 v2 _ _ hinv115 h64 h_v120 h_v2 (by ns_tac) (by ns_tac) as ⟨v121, s116, hinv116, h_v121⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 dropping h_v120 h_v2 hinv115 s115 v120 v2
  step as ⟨e_v122, he_v122⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s116 _ _ rfl hinv116 h64 as ⟨v122, s117, hinv117, h_v122⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 h_v121 dropping hinv116 s116
  replace h_v122 := Represents.rep_of_eq h_v122 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v122]; decide)
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo_Int.construct s117 e_v123 (by rw [he_v123]; exact empty_args) hinv117 h64 as ⟨v123, s118, hinv118, h_v123⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 h_v121 h_v122 dropping he_v122 he_v123 hinv117 e_v122 e_v123 s117
  step as ⟨e_v124, he_v124⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s118 e_v124 (by rw [he_v124]; rfl) h_v122 h_v123 hinv118 h64 as ⟨v124, s119, hinv119, h_v124⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 h_v121 dropping h_v122 h_v123 he_v124 hinv118 e_v124 s118 v122 v123
  store_step with Store.apply_rep s119 v121 v124 _ _ hinv119 h64 h_v121 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s120, hinv120, h_v125⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 dropping h_v121 h_v124 hinv119 s119 v121 v124
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s120 1#u32 (1) (by scalar_tac) hinv120 h64 as ⟨v126, s121, hinv121, h_v126⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 h_v125 dropping hinv120 s120
  store_step with Store.apply_rep s121 v125 v126 _ _ hinv121 h64 h_v125 h_v126 (by ns_tac) (by ns_tac) as ⟨v127, s122, hinv122, h_v127⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 h_v119 dropping h_v125 h_v126 hinv121 s121 v125 v126
  store_step with Store.apply_rep s122 v119 v127 _ _ hinv122 h64 h_v119 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s123, hinv123, h_v128⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v118 dropping h_v119 h_v127 hinv122 s122 v119 v127
  store_step with Store.apply_rep s123 v118 v128 _ _ hinv123 h64 h_v118 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s124, hinv124, h_v129⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 dropping h_v118 h_v128 hinv123 s123 v118 v128
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s124 e_v130 (by rw [he_v130]; exact empty_args) hinv124 h64 as ⟨v130, s125, hinv125, h_v130⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 dropping he_v130 hinv124 e_v130 s124
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s125 e_v131 (by rw [he_v131]; exact empty_args) hinv125 h64 as ⟨v131, s126, hinv126, h_v131⟩ growing hG carrying h_v5 h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 dropping he_v131 hinv125 e_v131 s125
  store_step with Store.apply_rep s126 v131 v5 _ _ hinv126 h64 h_v131 h_v5 (by ns_tac) (by ns_tac) as ⟨v132, s127, hinv127, h_v132⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 dropping h_v131 h_v5 hinv126 s126 v131 v5
  step as ⟨e_v133, he_v133⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s127 _ _ rfl hinv127 h64 as ⟨v133, s128, hinv128, h_v133⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 h_v132 dropping hinv127 s127
  replace h_v133 := Represents.rep_of_eq h_v133 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v133]; decide)
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo_Int.construct s128 e_v134 (by rw [he_v134]; exact empty_args) hinv128 h64 as ⟨v134, s129, hinv129, h_v134⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 h_v132 h_v133 dropping he_v133 he_v134 hinv128 e_v133 e_v134 s128
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s129 e_v135 (by rw [he_v135]; rfl) h_v133 h_v134 hinv129 h64 as ⟨v135, s130, hinv130, h_v135⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 h_v132 dropping h_v133 h_v134 he_v135 hinv129 e_v135 s129 v133 v134
  store_step with Store.apply_rep s130 v132 v135 _ _ hinv130 h64 h_v132 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s131, hinv131, h_v136⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 dropping h_v132 h_v135 hinv130 s130 v132 v135
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s131 1#u32 (1) (by scalar_tac) hinv131 h64 as ⟨v137, s132, hinv132, h_v137⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 h_v136 dropping hinv131 s131
  store_step with Store.apply_rep s132 v136 v137 _ _ hinv132 h64 h_v136 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s133, hinv133, h_v138⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 h_v130 dropping h_v136 h_v137 hinv132 s132 v136 v137
  store_step with Store.apply_rep s133 v130 v138 _ _ hinv133 h64 h_v130 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s134, hinv134, h_v139⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 h_v129 dropping h_v130 h_v138 hinv133 s133 v130 v138
  store_step with Store.apply_rep s134 v129 v139 _ _ hinv134 h64 h_v129 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s135, hinv135, h_v140⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 h_v117 dropping h_v129 h_v139 hinv134 s134 v129 v139
  store_step with Store.apply_rep s135 v117 v140 _ _ hinv135 h64 h_v117 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s136, hinv136, h_v141⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v86 dropping h_v117 h_v140 hinv135 s135 v117 v140
  store_step with Store.apply_rep s136 v86 v141 _ _ hinv136 h64 h_v86 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s137, hinv137, h_v142⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 dropping h_v141 h_v86 hinv136 s136 v141 v86
  store_step with Store.literal_boolean_spec s137 false hinv137 h64 as ⟨v143, s138, hinv138, h_v143⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 h_v142 dropping hinv137 s137
  store_step with Store.apply_rep s138 v142 v143 _ _ hinv138 h64 h_v142 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s139, hinv139, h_v144⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 h_v85 dropping h_v142 h_v143 hinv138 s138 v142 v143
  store_step with Store.apply_rep s139 v85 v144 _ _ hinv139 h64 h_v85 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s140, hinv140, h_v145⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 h_v62 dropping h_v144 h_v85 hinv139 s139 v144 v85
  store_step with Store.apply_rep s140 v62 v145 _ _ hinv140 h64 h_v62 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s141, hinv141, h_v146⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 h_v50 dropping h_v145 h_v62 hinv140 s140 v145 v62
  store_step with Store.apply_rep s141 v50 v146 _ _ hinv141 h64 h_v50 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s142, hinv142, h_v147⟩ growing hG carrying h_v17 h_v18 h_v27 h_v38 dropping h_v146 h_v50 hinv141 s141 v146 v50
  store_step with Store.apply_rep s142 v38 v147 _ _ hinv142 h64 h_v38 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s143, hinv143, h_v148⟩ growing hG carrying h_v17 h_v18 h_v27 dropping h_v147 h_v38 hinv142 s142 v147 v38
  store_step with Store.apply_rep s143 v27 v148 _ _ hinv143 h64 h_v27 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s144, hinv144, h_v149⟩ growing hG carrying h_v17 h_v18 dropping h_v148 h_v27 hinv143 s143 v148 v27
  store_step with Store.apply_rep s144 v18 v149 _ _ hinv144 h64 h_v18 h_v149 (by ns_tac) (by ns_tac) as ⟨v150, s145, hinv145, h_v150⟩ growing hG carrying h_v17 dropping h_v149 h_v18 hinv144 s144 v149 v18
  store_step with Store.apply_rep s145 v17 v150 _ _ hinv145 h64 h_v17 h_v150 (by ns_tac) (by ns_tac) as ⟨v151, s146, hinv146, h_v151⟩ growing hG carrying dropping h_v150 h_v17 hinv145 s145 v150 v17
  case_done hinv146 hG with h_v151 in EoCases.__str_reduction_pred.case_12 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 4380000 in
theorem case_13_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_13_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_13 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_13 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_13
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_13
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  store_step with Store.apply_rep s4 v6 v2 _ _ hinv4 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with Store.apply_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v7 hinv5 s5 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v8 dropping he_v9 hinv6 e_v9 s6
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__40purify.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping he_v10 hinv7 e_v10 s7
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 h_v10 dropping he_v11 hinv8 e_v11 s8
  store_step with Store.apply_rep s9 v11 v2 _ _ hinv9 h64 h_v11 h_v2 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 h_v10 dropping h_v11 hinv9 s9 v11
  store_step with Store.apply_rep s10 v10 v12 _ _ hinv10 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping h_v10 h_v12 hinv10 s10 v10 v12
  store_step with Store.apply_rep s11 v9 v13 _ _ hinv11 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v13 h_v9 hinv11 s11 v13 v9
  store_step with Store.apply_rep s12 v8 v14 _ _ hinv12 h64 h_v8 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v4 dropping h_v14 h_v8 hinv12 s12 v14 v8
  store_step with Store.apply_rep s13 v4 v15 _ _ hinv13 h64 h_v4 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 dropping h_v15 h_v4 hinv13 s13 v15 v4
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_and.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v16 dropping he_v17 hinv14 e_v17 s14
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_forall.construct s15 e_v18 (by rw [he_v18]; exact empty_args) hinv15 h64 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v16 h_v17 dropping he_v18 hinv15 e_v18 s15
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s16 e_v19 (by rw [he_v19]; exact empty_args) hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping he_v19 hinv16 e_v19 s16
  step as ⟨e_v20, he_v20⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s17 _ _ rfl hinv17 h64 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 dropping hinv17 s17
  replace h_v20 := Represents.rep_of_eq h_v20 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v20]; decide)
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_Int.construct s18 e_v21 (by rw [he_v21]; exact empty_args) hinv18 h64 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 h_v20 dropping he_v20 he_v21 hinv18 e_v20 e_v21 s18
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s19 e_v22 (by rw [he_v22]; rfl) h_v20 h_v21 hinv19 h64 as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 dropping h_v20 h_v21 he_v22 hinv19 e_v22 s19 v20 v21
  store_step with Store.apply_rep s20 v19 v22 _ _ hinv20 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping h_v19 h_v22 hinv20 s20 v19 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s21 e_v24 (by rw [he_v24]; exact empty_args) hinv21 h64 as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v23 dropping he_v24 hinv21 e_v24 s21
  store_step with Store.apply_rep s22 v23 v24 _ _ hinv22 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping h_v23 h_v24 hinv22 s22 v23 v24
  store_step with Store.apply_rep s23 v18 v25 _ _ hinv23 h64 h_v18 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_v2 h_v16 h_v17 dropping h_v18 h_v25 hinv23 s23 v18 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_or.construct s24 e_v27 (by rw [he_v27]; exact empty_args) hinv24 h64 as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 dropping he_v27 hinv24 e_v27 s24
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s25 e_v28 (by rw [he_v28]; exact empty_args) hinv25 h64 as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 dropping he_v28 hinv25 e_v28 s25
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3e_3d.construct s26 e_v29 (by rw [he_v29]; exact empty_args) hinv26 h64 as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping he_v29 hinv26 e_v29 s26
  step as ⟨e_v30, he_v30⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s27 _ _ rfl hinv27 h64 as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 dropping hinv27 s27
  replace h_v30 := Represents.rep_of_eq h_v30 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v30]; decide)
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_Int.construct s28 e_v31 (by rw [he_v31]; exact empty_args) hinv28 h64 as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 h_v30 dropping he_v30 he_v31 hinv28 e_v30 e_v31 s28
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s29 e_v32 (by rw [he_v32]; rfl) h_v30 h_v31 hinv29 h64 as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 dropping h_v30 h_v31 he_v32 hinv29 e_v32 s29 v30 v31
  store_step with Store.apply_rep s30 v29 v32 _ _ hinv30 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping h_v29 h_v32 hinv30 s30 v29 v32
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s31 0#u32 (0) (by scalar_tac) hinv31 h64 as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v33 dropping hinv31 s31
  store_step with Store.apply_rep s32 v33 v34 _ _ hinv32 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping h_v33 h_v34 hinv32 s32 v33 v34
  store_step with Store.apply_rep s33 v28 v35 _ _ hinv33 h64 h_v28 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 dropping h_v28 h_v35 hinv33 s33 v28 v35
  store_step with Store.apply_rep s34 v27 v36 _ _ hinv34 h64 h_v27 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 dropping h_v27 h_v36 hinv34 s34 v27 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_or.construct s35 e_v38 (by rw [he_v38]; exact empty_args) hinv35 h64 as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 dropping he_v38 hinv35 e_v38 s35
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_not.construct s36 e_v39 (by rw [he_v39]; exact empty_args) hinv36 h64 as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 dropping he_v39 hinv36 e_v39 s36
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3c.construct s37 e_v40 (by rw [he_v40]; exact empty_args) hinv37 h64 as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping he_v40 hinv37 e_v40 s37
  step as ⟨e_v41, he_v41⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s38 _ _ rfl hinv38 h64 as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 dropping hinv38 s38
  replace h_v41 := Represents.rep_of_eq h_v41 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v41]; decide)
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_Int.construct s39 e_v42 (by rw [he_v42]; exact empty_args) hinv39 h64 as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 h_v41 dropping he_v41 he_v42 hinv39 e_v41 e_v42 s39
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s40 e_v43 (by rw [he_v43]; rfl) h_v41 h_v42 hinv40 h64 as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 dropping h_v41 h_v42 he_v43 hinv40 e_v43 s40 v41 v42
  store_step with Store.apply_rep s41 v40 v43 _ _ hinv41 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping h_v40 h_v43 hinv41 s41 v40 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_str_2elen.construct s42 e_v45 (by rw [he_v45]; exact empty_args) hinv42 h64 as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 dropping he_v45 hinv42 e_v45 s42
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__40purify.construct s43 e_v46 (by rw [he_v46]; exact empty_args) hinv43 h64 as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 dropping he_v46 hinv43 e_v46 s43
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s44 e_v47 (by rw [he_v47]; exact empty_args) hinv44 h64 as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 h_v46 dropping he_v47 hinv44 e_v47 s44
  store_step with Store.apply_rep s45 v47 v2 _ _ hinv45 h64 h_v47 h_v2 (by ns_tac) (by ns_tac) as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 h_v46 dropping h_v47 hinv45 s45 v47
  store_step with Store.apply_rep s46 v46 v48 _ _ hinv46 h64 h_v46 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 dropping h_v46 h_v48 hinv46 s46 v46 v48
  store_step with Store.apply_rep s47 v45 v49 _ _ hinv47 h64 h_v45 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 dropping h_v45 h_v49 hinv47 s47 v45 v49
  store_step with Store.apply_rep s48 v44 v50 _ _ hinv48 h64 h_v44 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping h_v44 h_v50 hinv48 s48 v44 v50
  store_step with Store.apply_rep s49 v39 v51 _ _ hinv49 h64 h_v39 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 dropping h_v39 h_v51 hinv49 s49 v39 v51
  store_step with Store.apply_rep s50 v38 v52 _ _ hinv50 h64 h_v38 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 dropping h_v38 h_v52 hinv50 s50 v38 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_or.construct s51 e_v54 (by rw [he_v54]; exact empty_args) hinv51 h64 as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 dropping he_v54 hinv51 e_v54 s51
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__3d.construct s52 e_v55 (by rw [he_v55]; exact empty_args) hinv52 h64 as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping he_v55 hinv52 e_v55 s52
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s53 e_v56 (by rw [he_v56]; exact empty_args) hinv53 h64 as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping he_v56 hinv53 e_v56 s53
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s54 e_v57 (by rw [he_v57]; exact empty_args) hinv54 h64 as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping he_v57 hinv54 e_v57 s54
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__40purify.construct s55 e_v58 (by rw [he_v58]; exact empty_args) hinv55 h64 as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 dropping he_v58 hinv55 e_v58 s55
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s56 e_v59 (by rw [he_v59]; exact empty_args) hinv56 h64 as ⟨v59, s57, hinv57, h_v59⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 dropping he_v59 hinv56 e_v59 s56
  store_step with Store.apply_rep s57 v59 v2 _ _ hinv57 h64 h_v59 h_v2 (by ns_tac) (by ns_tac) as ⟨v60, s58, hinv58, h_v60⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 dropping h_v59 hinv57 s57 v59
  store_step with Store.apply_rep s58 v58 v60 _ _ hinv58 h64 h_v58 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s59, hinv59, h_v61⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 dropping h_v58 h_v60 hinv58 s58 v58 v60
  store_step with Store.apply_rep s59 v57 v61 _ _ hinv59 h64 h_v57 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s60, hinv60, h_v62⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v57 h_v61 hinv59 s59 v57 v61
  step as ⟨e_v63, he_v63⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s60 _ _ rfl hinv60 h64 as ⟨v63, s61, hinv61, h_v63⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v62 dropping hinv60 s60
  replace h_v63 := Represents.rep_of_eq h_v63 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v63]; decide)
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_Int.construct s61 e_v64 (by rw [he_v64]; exact empty_args) hinv61 h64 as ⟨v64, s62, hinv62, h_v64⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v62 h_v63 dropping he_v63 he_v64 hinv61 e_v63 e_v64 s61
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s62 e_v65 (by rw [he_v65]; rfl) h_v63 h_v64 hinv62 h64 as ⟨v65, s63, hinv63, h_v65⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v62 dropping h_v63 h_v64 he_v65 hinv62 e_v65 s62 v63 v64
  store_step with Store.apply_rep s63 v62 v65 _ _ hinv63 h64 h_v62 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s64, hinv64, h_v66⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v62 h_v65 hinv63 s63 v62 v65
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s64 1#u32 (1) (by scalar_tac) hinv64 h64 as ⟨v67, s65, hinv65, h_v67⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v66 dropping hinv64 s64
  store_step with Store.apply_rep s65 v66 v67 _ _ hinv65 h64 h_v66 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s66, hinv66, h_v68⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v66 h_v67 hinv65 s65 v66 v67
  store_step with Store.apply_rep s66 v56 v68 _ _ hinv66 h64 h_v56 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s67, hinv67, h_v69⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping h_v56 h_v68 hinv66 s66 v56 v68
  store_step with Store.apply_rep s67 v55 v69 _ _ hinv67 h64 h_v55 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s68, hinv68, h_v70⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping h_v55 h_v69 hinv67 s67 v55 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_ite.construct s68 e_v71 (by rw [he_v71]; exact empty_args) hinv68 h64 as ⟨v71, s69, hinv69, h_v71⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping he_v71 hinv68 e_v71 s68
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo_and.construct s69 e_v72 (by rw [he_v72]; exact empty_args) hinv69 h64 as ⟨v72, s70, hinv70, h_v72⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 dropping he_v72 hinv69 e_v72 s69
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo__3c_3d.construct s70 e_v73 (by rw [he_v73]; exact empty_args) hinv70 h64 as ⟨v73, s71, hinv71, h_v73⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 dropping he_v73 hinv70 e_v73 s70
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s71 65#u32 (65) (by scalar_tac) hinv71 h64 as ⟨v74, s72, hinv72, h_v74⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v73 dropping hinv71 s71
  store_step with Store.apply_rep s72 v73 v74 _ _ hinv72 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s73, hinv73, h_v75⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 dropping h_v73 h_v74 hinv72 s72 v73 v74
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s73 e_v76 (by rw [he_v76]; exact empty_args) hinv73 h64 as ⟨v76, s74, hinv74, h_v76⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 dropping he_v76 hinv73 e_v76 s73
  step as ⟨e_v77, he_v77⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s74 e_v77 (by rw [he_v77]; exact empty_args) hinv74 h64 as ⟨v77, s75, hinv75, h_v77⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping he_v77 hinv74 e_v77 s74
  store_step with Store.apply_rep s75 v77 v2 _ _ hinv75 h64 h_v77 h_v2 (by ns_tac) (by ns_tac) as ⟨v78, s76, hinv76, h_v78⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping h_v77 hinv75 s75 v77
  step as ⟨e_v79, he_v79⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s76 _ _ rfl hinv76 h64 as ⟨v79, s77, hinv77, h_v79⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v78 dropping hinv76 s76
  replace h_v79 := Represents.rep_of_eq h_v79 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v79]; decide)
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_Int.construct s77 e_v80 (by rw [he_v80]; exact empty_args) hinv77 h64 as ⟨v80, s78, hinv78, h_v80⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v78 h_v79 dropping he_v79 he_v80 hinv77 e_v79 e_v80 s77
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s78 e_v81 (by rw [he_v81]; rfl) h_v79 h_v80 hinv78 h64 as ⟨v81, s79, hinv79, h_v81⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v78 dropping h_v79 h_v80 he_v81 hinv78 e_v81 s78 v79 v80
  store_step with Store.apply_rep s79 v78 v81 _ _ hinv79 h64 h_v78 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s80, hinv80, h_v82⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping h_v78 h_v81 hinv79 s79 v78 v81
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s80 1#u32 (1) (by scalar_tac) hinv80 h64 as ⟨v83, s81, hinv81, h_v83⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v82 dropping hinv80 s80
  store_step with Store.apply_rep s81 v82 v83 _ _ hinv81 h64 h_v82 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s82, hinv82, h_v84⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping h_v82 h_v83 hinv81 s81 v82 v83
  store_step with Store.apply_rep s82 v76 v84 _ _ hinv82 h64 h_v76 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s83, hinv83, h_v85⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 dropping h_v76 h_v84 hinv82 s82 v76 v84
  store_step with Store.apply_rep s83 v75 v85 _ _ hinv83 h64 h_v75 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s84, hinv84, h_v86⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 dropping h_v75 h_v85 hinv83 s83 v75 v85
  store_step with Store.apply_rep s84 v72 v86 _ _ hinv84 h64 h_v72 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s85, hinv85, h_v87⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 dropping h_v72 h_v86 hinv84 s84 v72 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_and.construct s85 e_v88 (by rw [he_v88]; exact empty_args) hinv85 h64 as ⟨v88, s86, hinv86, h_v88⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 dropping he_v88 hinv85 e_v88 s85
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo__3c_3d.construct s86 e_v89 (by rw [he_v89]; exact empty_args) hinv86 h64 as ⟨v89, s87, hinv87, h_v89⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 dropping he_v89 hinv86 e_v89 s86
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s87 e_v90 (by rw [he_v90]; exact empty_args) hinv87 h64 as ⟨v90, s88, hinv88, h_v90⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 dropping he_v90 hinv87 e_v90 s87
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s88 e_v91 (by rw [he_v91]; exact empty_args) hinv88 h64 as ⟨v91, s89, hinv89, h_v91⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping he_v91 hinv88 e_v91 s88
  store_step with Store.apply_rep s89 v91 v2 _ _ hinv89 h64 h_v91 h_v2 (by ns_tac) (by ns_tac) as ⟨v92, s90, hinv90, h_v92⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping h_v91 hinv89 s89 v91
  step as ⟨e_v93, he_v93⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s90 _ _ rfl hinv90 h64 as ⟨v93, s91, hinv91, h_v93⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v92 dropping hinv90 s90
  replace h_v93 := Represents.rep_of_eq h_v93 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v93]; decide)
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo_Int.construct s91 e_v94 (by rw [he_v94]; exact empty_args) hinv91 h64 as ⟨v94, s92, hinv92, h_v94⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v92 h_v93 dropping he_v93 he_v94 hinv91 e_v93 e_v94 s91
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s92 e_v95 (by rw [he_v95]; rfl) h_v93 h_v94 hinv92 h64 as ⟨v95, s93, hinv93, h_v95⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v92 dropping h_v93 h_v94 he_v95 hinv92 e_v95 s92 v93 v94
  store_step with Store.apply_rep s93 v92 v95 _ _ hinv93 h64 h_v92 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s94, hinv94, h_v96⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping h_v92 h_v95 hinv93 s93 v92 v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s94 1#u32 (1) (by scalar_tac) hinv94 h64 as ⟨v97, s95, hinv95, h_v97⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v96 dropping hinv94 s94
  store_step with Store.apply_rep s95 v96 v97 _ _ hinv95 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s96, hinv96, h_v98⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping h_v96 h_v97 hinv95 s95 v96 v97
  store_step with Store.apply_rep s96 v90 v98 _ _ hinv96 h64 h_v90 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s97, hinv97, h_v99⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 dropping h_v90 h_v98 hinv96 s96 v90 v98
  store_step with Store.apply_rep s97 v89 v99 _ _ hinv97 h64 h_v89 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s98, hinv98, h_v100⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 dropping h_v89 h_v99 hinv97 s97 v89 v99
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s98 90#u32 (90) (by scalar_tac) hinv98 h64 as ⟨v101, s99, hinv99, h_v101⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v100 dropping hinv98 s98
  store_step with Store.apply_rep s99 v100 v101 _ _ hinv99 h64 h_v100 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s100, hinv100, h_v102⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 dropping h_v100 h_v101 hinv99 s99 v100 v101
  store_step with Store.apply_rep s100 v88 v102 _ _ hinv100 h64 h_v88 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s101, hinv101, h_v103⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 dropping h_v102 h_v88 hinv100 s100 v102 v88
  store_step with Store.literal_boolean_spec s101 true hinv101 h64 as ⟨v104, s102, hinv102, h_v104⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v103 dropping hinv101 s101
  store_step with Store.apply_rep s102 v103 v104 _ _ hinv102 h64 h_v103 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s103, hinv103, h_v105⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 dropping h_v103 h_v104 hinv102 s102 v103 v104
  store_step with Store.apply_rep s103 v87 v105 _ _ hinv103 h64 h_v87 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s104, hinv104, h_v106⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 dropping h_v105 h_v87 hinv103 s103 v105 v87
  store_step with Store.apply_rep s104 v71 v106 _ _ hinv104 h64 h_v71 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s105, hinv105, h_v107⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping h_v106 h_v71 hinv104 s104 v106 v71
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo__2b.construct s105 e_v108 (by rw [he_v108]; exact empty_args) hinv105 h64 as ⟨v108, s106, hinv106, h_v108⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 dropping he_v108 hinv105 e_v108 s105
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s106 e_v109 (by rw [he_v109]; exact empty_args) hinv106 h64 as ⟨v109, s107, hinv107, h_v109⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 dropping he_v109 hinv106 e_v109 s106
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s107 e_v110 (by rw [he_v110]; exact empty_args) hinv107 h64 as ⟨v110, s108, hinv108, h_v110⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping he_v110 hinv107 e_v110 s107
  store_step with Store.apply_rep s108 v110 v2 _ _ hinv108 h64 h_v110 h_v2 (by ns_tac) (by ns_tac) as ⟨v111, s109, hinv109, h_v111⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping h_v110 hinv108 s108 v110
  step as ⟨e_v112, he_v112⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s109 _ _ rfl hinv109 h64 as ⟨v112, s110, hinv110, h_v112⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v111 dropping hinv109 s109
  replace h_v112 := Represents.rep_of_eq h_v112 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v112]; decide)
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_Int.construct s110 e_v113 (by rw [he_v113]; exact empty_args) hinv110 h64 as ⟨v113, s111, hinv111, h_v113⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v111 h_v112 dropping he_v112 he_v113 hinv110 e_v112 e_v113 s110
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s111 e_v114 (by rw [he_v114]; rfl) h_v112 h_v113 hinv111 h64 as ⟨v114, s112, hinv112, h_v114⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v111 dropping h_v112 h_v113 he_v114 hinv111 e_v114 s111 v112 v113
  store_step with Store.apply_rep s112 v111 v114 _ _ hinv112 h64 h_v111 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s113, hinv113, h_v115⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping h_v111 h_v114 hinv112 s112 v111 v114
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s113 1#u32 (1) (by scalar_tac) hinv113 h64 as ⟨v116, s114, hinv114, h_v116⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v115 dropping hinv113 s113
  store_step with Store.apply_rep s114 v115 v116 _ _ hinv114 h64 h_v115 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s115, hinv115, h_v117⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping h_v115 h_v116 hinv114 s114 v115 v116
  store_step with Store.apply_rep s115 v109 v117 _ _ hinv115 h64 h_v109 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s116, hinv116, h_v118⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 dropping h_v109 h_v117 hinv115 s115 v109 v117
  store_step with Store.apply_rep s116 v108 v118 _ _ hinv116 h64 h_v108 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s117, hinv117, h_v119⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 dropping h_v108 h_v118 hinv116 s116 v108 v118
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__2b.construct s117 e_v120 (by rw [he_v120]; exact empty_args) hinv117 h64 as ⟨v120, s118, hinv118, h_v120⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 dropping he_v120 hinv117 e_v120 s117
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s118 32#u32 (32) (by scalar_tac) hinv118 h64 as ⟨v121, s119, hinv119, h_v121⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 h_v120 dropping hinv118 s118
  store_step with Store.apply_rep s119 v120 v121 _ _ hinv119 h64 h_v120 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s120, hinv120, h_v122⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 dropping h_v120 h_v121 hinv119 s119 v120 v121
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s120 0#u32 (0) (by scalar_tac) hinv120 h64 as ⟨v123, s121, hinv121, h_v123⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 h_v122 dropping hinv120 s120
  store_step with Store.apply_rep s121 v122 v123 _ _ hinv121 h64 h_v122 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s122, hinv122, h_v124⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 dropping h_v122 h_v123 hinv121 s121 v122 v123
  store_step with Store.apply_rep s122 v119 v124 _ _ hinv122 h64 h_v119 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s123, hinv123, h_v125⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 dropping h_v119 h_v124 hinv122 s122 v119 v124
  store_step with Store.apply_rep s123 v107 v125 _ _ hinv123 h64 h_v107 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s124, hinv124, h_v126⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping h_v107 h_v125 hinv123 s123 v107 v125
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s124 e_v127 (by rw [he_v127]; exact empty_args) hinv124 h64 as ⟨v127, s125, hinv125, h_v127⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 dropping he_v127 hinv124 e_v127 s124
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s125 e_v128 (by rw [he_v128]; exact empty_args) hinv125 h64 as ⟨v128, s126, hinv126, h_v128⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping he_v128 hinv125 e_v128 s125
  store_step with Store.apply_rep s126 v128 v2 _ _ hinv126 h64 h_v128 h_v2 (by ns_tac) (by ns_tac) as ⟨v129, s127, hinv127, h_v129⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping h_v128 h_v2 hinv126 s126 v128 v2
  step as ⟨e_v130, he_v130⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s127 _ _ rfl hinv127 h64 as ⟨v130, s128, hinv128, h_v130⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v129 dropping hinv127 s127
  replace h_v130 := Represents.rep_of_eq h_v130 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v130]; decide)
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_Int.construct s128 e_v131 (by rw [he_v131]; exact empty_args) hinv128 h64 as ⟨v131, s129, hinv129, h_v131⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v129 h_v130 dropping he_v130 he_v131 hinv128 e_v130 e_v131 s128
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s129 e_v132 (by rw [he_v132]; rfl) h_v130 h_v131 hinv129 h64 as ⟨v132, s130, hinv130, h_v132⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v129 dropping h_v130 h_v131 he_v132 hinv129 e_v132 s129 v130 v131
  store_step with Store.apply_rep s130 v129 v132 _ _ hinv130 h64 h_v129 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s131, hinv131, h_v133⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping h_v129 h_v132 hinv130 s130 v129 v132
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s131 1#u32 (1) (by scalar_tac) hinv131 h64 as ⟨v134, s132, hinv132, h_v134⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v133 dropping hinv131 s131
  store_step with Store.apply_rep s132 v133 v134 _ _ hinv132 h64 h_v133 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s133, hinv133, h_v135⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping h_v133 h_v134 hinv132 s132 v133 v134
  store_step with Store.apply_rep s133 v127 v135 _ _ hinv133 h64 h_v127 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s134, hinv134, h_v136⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 dropping h_v127 h_v135 hinv133 s133 v127 v135
  store_step with Store.apply_rep s134 v126 v136 _ _ hinv134 h64 h_v126 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s135, hinv135, h_v137⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping h_v126 h_v136 hinv134 s134 v126 v136
  store_step with Store.apply_rep s135 v70 v137 _ _ hinv135 h64 h_v70 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s136, hinv136, h_v138⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping h_v137 h_v70 hinv135 s135 v137 v70
  store_step with Store.apply_rep s136 v54 v138 _ _ hinv136 h64 h_v54 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s137, hinv137, h_v139⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 dropping h_v138 h_v54 hinv136 s136 v138 v54
  store_step with Store.literal_boolean_spec s137 false hinv137 h64 as ⟨v140, s138, hinv138, h_v140⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v139 dropping hinv137 s137
  store_step with Store.apply_rep s138 v139 v140 _ _ hinv138 h64 h_v139 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s139, hinv139, h_v141⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 dropping h_v139 h_v140 hinv138 s138 v139 v140
  store_step with Store.apply_rep s139 v53 v141 _ _ hinv139 h64 h_v53 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s140, hinv140, h_v142⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 dropping h_v141 h_v53 hinv139 s139 v141 v53
  store_step with Store.apply_rep s140 v37 v142 _ _ hinv140 h64 h_v37 h_v142 (by ns_tac) (by ns_tac) as ⟨v143, s141, hinv141, h_v143⟩ growing hG carrying h_v16 h_v17 h_v26 dropping h_v142 h_v37 hinv140 s140 v142 v37
  store_step with Store.apply_rep s141 v26 v143 _ _ hinv141 h64 h_v26 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s142, hinv142, h_v144⟩ growing hG carrying h_v16 h_v17 dropping h_v143 h_v26 hinv141 s141 v143 v26
  store_step with Store.apply_rep s142 v17 v144 _ _ hinv142 h64 h_v17 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s143, hinv143, h_v145⟩ growing hG carrying h_v16 dropping h_v144 h_v17 hinv142 s142 v144 v17
  store_step with Store.literal_boolean_spec s143 true hinv143 h64 as ⟨v146, s144, hinv144, h_v146⟩ growing hG carrying h_v16 h_v145 dropping hinv143 s143
  store_step with Store.apply_rep s144 v145 v146 _ _ hinv144 h64 h_v145 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s145, hinv145, h_v147⟩ growing hG carrying h_v16 dropping h_v145 h_v146 hinv144 s144 v145 v146
  store_step with Store.apply_rep s145 v16 v147 _ _ hinv145 h64 h_v16 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s146, hinv146, h_v148⟩ growing hG carrying dropping h_v147 h_v16 hinv145 s145 v147 v16
  case_done hinv146 hG with h_v148 in EoCases.__str_reduction_pred.case_13 using hn_a0 hn_v1 hn_v2

set_option maxHeartbeats 4380000 in
theorem case_14_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_14_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_14 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_14 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_14
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_14
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  store_step with Store.apply_rep s4 v6 v2 _ _ hinv4 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with Store.apply_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v7 hinv5 s5 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v8 dropping he_v9 hinv6 e_v9 s6
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__40purify.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping he_v10 hinv7 e_v10 s7
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 h_v10 dropping he_v11 hinv8 e_v11 s8
  store_step with Store.apply_rep s9 v11 v2 _ _ hinv9 h64 h_v11 h_v2 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 h_v10 dropping h_v11 hinv9 s9 v11
  store_step with Store.apply_rep s10 v10 v12 _ _ hinv10 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping h_v10 h_v12 hinv10 s10 v10 v12
  store_step with Store.apply_rep s11 v9 v13 _ _ hinv11 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v13 h_v9 hinv11 s11 v13 v9
  store_step with Store.apply_rep s12 v8 v14 _ _ hinv12 h64 h_v8 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v4 dropping h_v14 h_v8 hinv12 s12 v14 v8
  store_step with Store.apply_rep s13 v4 v15 _ _ hinv13 h64 h_v4 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 dropping h_v15 h_v4 hinv13 s13 v15 v4
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_and.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v16 dropping he_v17 hinv14 e_v17 s14
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_forall.construct s15 e_v18 (by rw [he_v18]; exact empty_args) hinv15 h64 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v16 h_v17 dropping he_v18 hinv15 e_v18 s15
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s16 e_v19 (by rw [he_v19]; exact empty_args) hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping he_v19 hinv16 e_v19 s16
  step as ⟨e_v20, he_v20⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s17 _ _ rfl hinv17 h64 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 dropping hinv17 s17
  replace h_v20 := Represents.rep_of_eq h_v20 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v20]; decide)
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_Int.construct s18 e_v21 (by rw [he_v21]; exact empty_args) hinv18 h64 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 h_v20 dropping he_v20 he_v21 hinv18 e_v20 e_v21 s18
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s19 e_v22 (by rw [he_v22]; rfl) h_v20 h_v21 hinv19 h64 as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 dropping h_v20 h_v21 he_v22 hinv19 e_v22 s19 v20 v21
  store_step with Store.apply_rep s20 v19 v22 _ _ hinv20 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping h_v19 h_v22 hinv20 s20 v19 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s21 e_v24 (by rw [he_v24]; exact empty_args) hinv21 h64 as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v23 dropping he_v24 hinv21 e_v24 s21
  store_step with Store.apply_rep s22 v23 v24 _ _ hinv22 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping h_v23 h_v24 hinv22 s22 v23 v24
  store_step with Store.apply_rep s23 v18 v25 _ _ hinv23 h64 h_v18 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_v2 h_v16 h_v17 dropping h_v18 h_v25 hinv23 s23 v18 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_or.construct s24 e_v27 (by rw [he_v27]; exact empty_args) hinv24 h64 as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 dropping he_v27 hinv24 e_v27 s24
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s25 e_v28 (by rw [he_v28]; exact empty_args) hinv25 h64 as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 dropping he_v28 hinv25 e_v28 s25
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3e_3d.construct s26 e_v29 (by rw [he_v29]; exact empty_args) hinv26 h64 as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping he_v29 hinv26 e_v29 s26
  step as ⟨e_v30, he_v30⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s27 _ _ rfl hinv27 h64 as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 dropping hinv27 s27
  replace h_v30 := Represents.rep_of_eq h_v30 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v30]; decide)
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_Int.construct s28 e_v31 (by rw [he_v31]; exact empty_args) hinv28 h64 as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 h_v30 dropping he_v30 he_v31 hinv28 e_v30 e_v31 s28
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s29 e_v32 (by rw [he_v32]; rfl) h_v30 h_v31 hinv29 h64 as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 dropping h_v30 h_v31 he_v32 hinv29 e_v32 s29 v30 v31
  store_step with Store.apply_rep s30 v29 v32 _ _ hinv30 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping h_v29 h_v32 hinv30 s30 v29 v32
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s31 0#u32 (0) (by scalar_tac) hinv31 h64 as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v33 dropping hinv31 s31
  store_step with Store.apply_rep s32 v33 v34 _ _ hinv32 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping h_v33 h_v34 hinv32 s32 v33 v34
  store_step with Store.apply_rep s33 v28 v35 _ _ hinv33 h64 h_v28 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 dropping h_v28 h_v35 hinv33 s33 v28 v35
  store_step with Store.apply_rep s34 v27 v36 _ _ hinv34 h64 h_v27 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 dropping h_v27 h_v36 hinv34 s34 v27 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_or.construct s35 e_v38 (by rw [he_v38]; exact empty_args) hinv35 h64 as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 dropping he_v38 hinv35 e_v38 s35
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_not.construct s36 e_v39 (by rw [he_v39]; exact empty_args) hinv36 h64 as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 dropping he_v39 hinv36 e_v39 s36
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3c.construct s37 e_v40 (by rw [he_v40]; exact empty_args) hinv37 h64 as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping he_v40 hinv37 e_v40 s37
  step as ⟨e_v41, he_v41⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s38 _ _ rfl hinv38 h64 as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 dropping hinv38 s38
  replace h_v41 := Represents.rep_of_eq h_v41 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v41]; decide)
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_Int.construct s39 e_v42 (by rw [he_v42]; exact empty_args) hinv39 h64 as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 h_v41 dropping he_v41 he_v42 hinv39 e_v41 e_v42 s39
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s40 e_v43 (by rw [he_v43]; rfl) h_v41 h_v42 hinv40 h64 as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 dropping h_v41 h_v42 he_v43 hinv40 e_v43 s40 v41 v42
  store_step with Store.apply_rep s41 v40 v43 _ _ hinv41 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping h_v40 h_v43 hinv41 s41 v40 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_str_2elen.construct s42 e_v45 (by rw [he_v45]; exact empty_args) hinv42 h64 as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 dropping he_v45 hinv42 e_v45 s42
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__40purify.construct s43 e_v46 (by rw [he_v46]; exact empty_args) hinv43 h64 as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 dropping he_v46 hinv43 e_v46 s43
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s44 e_v47 (by rw [he_v47]; exact empty_args) hinv44 h64 as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 h_v46 dropping he_v47 hinv44 e_v47 s44
  store_step with Store.apply_rep s45 v47 v2 _ _ hinv45 h64 h_v47 h_v2 (by ns_tac) (by ns_tac) as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 h_v46 dropping h_v47 hinv45 s45 v47
  store_step with Store.apply_rep s46 v46 v48 _ _ hinv46 h64 h_v46 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 dropping h_v46 h_v48 hinv46 s46 v46 v48
  store_step with Store.apply_rep s47 v45 v49 _ _ hinv47 h64 h_v45 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 dropping h_v45 h_v49 hinv47 s47 v45 v49
  store_step with Store.apply_rep s48 v44 v50 _ _ hinv48 h64 h_v44 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping h_v44 h_v50 hinv48 s48 v44 v50
  store_step with Store.apply_rep s49 v39 v51 _ _ hinv49 h64 h_v39 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 dropping h_v39 h_v51 hinv49 s49 v39 v51
  store_step with Store.apply_rep s50 v38 v52 _ _ hinv50 h64 h_v38 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 dropping h_v38 h_v52 hinv50 s50 v38 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_or.construct s51 e_v54 (by rw [he_v54]; exact empty_args) hinv51 h64 as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 dropping he_v54 hinv51 e_v54 s51
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__3d.construct s52 e_v55 (by rw [he_v55]; exact empty_args) hinv52 h64 as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping he_v55 hinv52 e_v55 s52
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s53 e_v56 (by rw [he_v56]; exact empty_args) hinv53 h64 as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping he_v56 hinv53 e_v56 s53
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s54 e_v57 (by rw [he_v57]; exact empty_args) hinv54 h64 as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping he_v57 hinv54 e_v57 s54
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__40purify.construct s55 e_v58 (by rw [he_v58]; exact empty_args) hinv55 h64 as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 dropping he_v58 hinv55 e_v58 s55
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s56 e_v59 (by rw [he_v59]; exact empty_args) hinv56 h64 as ⟨v59, s57, hinv57, h_v59⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 dropping he_v59 hinv56 e_v59 s56
  store_step with Store.apply_rep s57 v59 v2 _ _ hinv57 h64 h_v59 h_v2 (by ns_tac) (by ns_tac) as ⟨v60, s58, hinv58, h_v60⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 dropping h_v59 hinv57 s57 v59
  store_step with Store.apply_rep s58 v58 v60 _ _ hinv58 h64 h_v58 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s59, hinv59, h_v61⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 dropping h_v58 h_v60 hinv58 s58 v58 v60
  store_step with Store.apply_rep s59 v57 v61 _ _ hinv59 h64 h_v57 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s60, hinv60, h_v62⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v57 h_v61 hinv59 s59 v57 v61
  step as ⟨e_v63, he_v63⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s60 _ _ rfl hinv60 h64 as ⟨v63, s61, hinv61, h_v63⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v62 dropping hinv60 s60
  replace h_v63 := Represents.rep_of_eq h_v63 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v63]; decide)
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_Int.construct s61 e_v64 (by rw [he_v64]; exact empty_args) hinv61 h64 as ⟨v64, s62, hinv62, h_v64⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v62 h_v63 dropping he_v63 he_v64 hinv61 e_v63 e_v64 s61
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s62 e_v65 (by rw [he_v65]; rfl) h_v63 h_v64 hinv62 h64 as ⟨v65, s63, hinv63, h_v65⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v62 dropping h_v63 h_v64 he_v65 hinv62 e_v65 s62 v63 v64
  store_step with Store.apply_rep s63 v62 v65 _ _ hinv63 h64 h_v62 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s64, hinv64, h_v66⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v62 h_v65 hinv63 s63 v62 v65
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s64 1#u32 (1) (by scalar_tac) hinv64 h64 as ⟨v67, s65, hinv65, h_v67⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v66 dropping hinv64 s64
  store_step with Store.apply_rep s65 v66 v67 _ _ hinv65 h64 h_v66 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s66, hinv66, h_v68⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v66 h_v67 hinv65 s65 v66 v67
  store_step with Store.apply_rep s66 v56 v68 _ _ hinv66 h64 h_v56 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s67, hinv67, h_v69⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping h_v56 h_v68 hinv66 s66 v56 v68
  store_step with Store.apply_rep s67 v55 v69 _ _ hinv67 h64 h_v55 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s68, hinv68, h_v70⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping h_v55 h_v69 hinv67 s67 v55 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_ite.construct s68 e_v71 (by rw [he_v71]; exact empty_args) hinv68 h64 as ⟨v71, s69, hinv69, h_v71⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping he_v71 hinv68 e_v71 s68
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo_and.construct s69 e_v72 (by rw [he_v72]; exact empty_args) hinv69 h64 as ⟨v72, s70, hinv70, h_v72⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 dropping he_v72 hinv69 e_v72 s69
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo__3c_3d.construct s70 e_v73 (by rw [he_v73]; exact empty_args) hinv70 h64 as ⟨v73, s71, hinv71, h_v73⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 dropping he_v73 hinv70 e_v73 s70
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s71 97#u32 (97) (by scalar_tac) hinv71 h64 as ⟨v74, s72, hinv72, h_v74⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v73 dropping hinv71 s71
  store_step with Store.apply_rep s72 v73 v74 _ _ hinv72 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s73, hinv73, h_v75⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 dropping h_v73 h_v74 hinv72 s72 v73 v74
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s73 e_v76 (by rw [he_v76]; exact empty_args) hinv73 h64 as ⟨v76, s74, hinv74, h_v76⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 dropping he_v76 hinv73 e_v76 s73
  step as ⟨e_v77, he_v77⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s74 e_v77 (by rw [he_v77]; exact empty_args) hinv74 h64 as ⟨v77, s75, hinv75, h_v77⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping he_v77 hinv74 e_v77 s74
  store_step with Store.apply_rep s75 v77 v2 _ _ hinv75 h64 h_v77 h_v2 (by ns_tac) (by ns_tac) as ⟨v78, s76, hinv76, h_v78⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping h_v77 hinv75 s75 v77
  step as ⟨e_v79, he_v79⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s76 _ _ rfl hinv76 h64 as ⟨v79, s77, hinv77, h_v79⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v78 dropping hinv76 s76
  replace h_v79 := Represents.rep_of_eq h_v79 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v79]; decide)
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_Int.construct s77 e_v80 (by rw [he_v80]; exact empty_args) hinv77 h64 as ⟨v80, s78, hinv78, h_v80⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v78 h_v79 dropping he_v79 he_v80 hinv77 e_v79 e_v80 s77
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s78 e_v81 (by rw [he_v81]; rfl) h_v79 h_v80 hinv78 h64 as ⟨v81, s79, hinv79, h_v81⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v78 dropping h_v79 h_v80 he_v81 hinv78 e_v81 s78 v79 v80
  store_step with Store.apply_rep s79 v78 v81 _ _ hinv79 h64 h_v78 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s80, hinv80, h_v82⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping h_v78 h_v81 hinv79 s79 v78 v81
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s80 1#u32 (1) (by scalar_tac) hinv80 h64 as ⟨v83, s81, hinv81, h_v83⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 h_v82 dropping hinv80 s80
  store_step with Store.apply_rep s81 v82 v83 _ _ hinv81 h64 h_v82 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s82, hinv82, h_v84⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 h_v76 dropping h_v82 h_v83 hinv81 s81 v82 v83
  store_step with Store.apply_rep s82 v76 v84 _ _ hinv82 h64 h_v76 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s83, hinv83, h_v85⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 h_v75 dropping h_v76 h_v84 hinv82 s82 v76 v84
  store_step with Store.apply_rep s83 v75 v85 _ _ hinv83 h64 h_v75 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s84, hinv84, h_v86⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v72 dropping h_v75 h_v85 hinv83 s83 v75 v85
  store_step with Store.apply_rep s84 v72 v86 _ _ hinv84 h64 h_v72 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s85, hinv85, h_v87⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 dropping h_v72 h_v86 hinv84 s84 v72 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_and.construct s85 e_v88 (by rw [he_v88]; exact empty_args) hinv85 h64 as ⟨v88, s86, hinv86, h_v88⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 dropping he_v88 hinv85 e_v88 s85
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo__3c_3d.construct s86 e_v89 (by rw [he_v89]; exact empty_args) hinv86 h64 as ⟨v89, s87, hinv87, h_v89⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 dropping he_v89 hinv86 e_v89 s86
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s87 e_v90 (by rw [he_v90]; exact empty_args) hinv87 h64 as ⟨v90, s88, hinv88, h_v90⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 dropping he_v90 hinv87 e_v90 s87
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s88 e_v91 (by rw [he_v91]; exact empty_args) hinv88 h64 as ⟨v91, s89, hinv89, h_v91⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping he_v91 hinv88 e_v91 s88
  store_step with Store.apply_rep s89 v91 v2 _ _ hinv89 h64 h_v91 h_v2 (by ns_tac) (by ns_tac) as ⟨v92, s90, hinv90, h_v92⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping h_v91 hinv89 s89 v91
  step as ⟨e_v93, he_v93⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s90 _ _ rfl hinv90 h64 as ⟨v93, s91, hinv91, h_v93⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v92 dropping hinv90 s90
  replace h_v93 := Represents.rep_of_eq h_v93 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v93]; decide)
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo_Int.construct s91 e_v94 (by rw [he_v94]; exact empty_args) hinv91 h64 as ⟨v94, s92, hinv92, h_v94⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v92 h_v93 dropping he_v93 he_v94 hinv91 e_v93 e_v94 s91
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s92 e_v95 (by rw [he_v95]; rfl) h_v93 h_v94 hinv92 h64 as ⟨v95, s93, hinv93, h_v95⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v92 dropping h_v93 h_v94 he_v95 hinv92 e_v95 s92 v93 v94
  store_step with Store.apply_rep s93 v92 v95 _ _ hinv93 h64 h_v92 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s94, hinv94, h_v96⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping h_v92 h_v95 hinv93 s93 v92 v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s94 1#u32 (1) (by scalar_tac) hinv94 h64 as ⟨v97, s95, hinv95, h_v97⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 h_v96 dropping hinv94 s94
  store_step with Store.apply_rep s95 v96 v97 _ _ hinv95 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s96, hinv96, h_v98⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 h_v90 dropping h_v96 h_v97 hinv95 s95 v96 v97
  store_step with Store.apply_rep s96 v90 v98 _ _ hinv96 h64 h_v90 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s97, hinv97, h_v99⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v89 dropping h_v90 h_v98 hinv96 s96 v90 v98
  store_step with Store.apply_rep s97 v89 v99 _ _ hinv97 h64 h_v89 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s98, hinv98, h_v100⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 dropping h_v89 h_v99 hinv97 s97 v89 v99
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s98 122#u32 (122) (by scalar_tac) hinv98 h64 as ⟨v101, s99, hinv99, h_v101⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 h_v100 dropping hinv98 s98
  store_step with Store.apply_rep s99 v100 v101 _ _ hinv99 h64 h_v100 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s100, hinv100, h_v102⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v88 dropping h_v100 h_v101 hinv99 s99 v100 v101
  store_step with Store.apply_rep s100 v88 v102 _ _ hinv100 h64 h_v88 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s101, hinv101, h_v103⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 dropping h_v102 h_v88 hinv100 s100 v102 v88
  store_step with Store.literal_boolean_spec s101 true hinv101 h64 as ⟨v104, s102, hinv102, h_v104⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 h_v103 dropping hinv101 s101
  store_step with Store.apply_rep s102 v103 v104 _ _ hinv102 h64 h_v103 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s103, hinv103, h_v105⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 h_v87 dropping h_v103 h_v104 hinv102 s102 v103 v104
  store_step with Store.apply_rep s103 v87 v105 _ _ hinv103 h64 h_v87 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s104, hinv104, h_v106⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v71 dropping h_v105 h_v87 hinv103 s103 v105 v87
  store_step with Store.apply_rep s104 v71 v106 _ _ hinv104 h64 h_v71 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s105, hinv105, h_v107⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping h_v106 h_v71 hinv104 s104 v106 v71
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo__2b.construct s105 e_v108 (by rw [he_v108]; exact empty_args) hinv105 h64 as ⟨v108, s106, hinv106, h_v108⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 dropping he_v108 hinv105 e_v108 s105
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s106 e_v109 (by rw [he_v109]; exact empty_args) hinv106 h64 as ⟨v109, s107, hinv107, h_v109⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 dropping he_v109 hinv106 e_v109 s106
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s107 e_v110 (by rw [he_v110]; exact empty_args) hinv107 h64 as ⟨v110, s108, hinv108, h_v110⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping he_v110 hinv107 e_v110 s107
  store_step with Store.apply_rep s108 v110 v2 _ _ hinv108 h64 h_v110 h_v2 (by ns_tac) (by ns_tac) as ⟨v111, s109, hinv109, h_v111⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping h_v110 hinv108 s108 v110
  step as ⟨e_v112, he_v112⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s109 _ _ rfl hinv109 h64 as ⟨v112, s110, hinv110, h_v112⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v111 dropping hinv109 s109
  replace h_v112 := Represents.rep_of_eq h_v112 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v112]; decide)
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_Int.construct s110 e_v113 (by rw [he_v113]; exact empty_args) hinv110 h64 as ⟨v113, s111, hinv111, h_v113⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v111 h_v112 dropping he_v112 he_v113 hinv110 e_v112 e_v113 s110
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s111 e_v114 (by rw [he_v114]; rfl) h_v112 h_v113 hinv111 h64 as ⟨v114, s112, hinv112, h_v114⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v111 dropping h_v112 h_v113 he_v114 hinv111 e_v114 s111 v112 v113
  store_step with Store.apply_rep s112 v111 v114 _ _ hinv112 h64 h_v111 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s113, hinv113, h_v115⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping h_v111 h_v114 hinv112 s112 v111 v114
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s113 1#u32 (1) (by scalar_tac) hinv113 h64 as ⟨v116, s114, hinv114, h_v116⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 h_v115 dropping hinv113 s113
  store_step with Store.apply_rep s114 v115 v116 _ _ hinv114 h64 h_v115 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s115, hinv115, h_v117⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 h_v109 dropping h_v115 h_v116 hinv114 s114 v115 v116
  store_step with Store.apply_rep s115 v109 v117 _ _ hinv115 h64 h_v109 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s116, hinv116, h_v118⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v108 dropping h_v109 h_v117 hinv115 s115 v109 v117
  store_step with Store.apply_rep s116 v108 v118 _ _ hinv116 h64 h_v108 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s117, hinv117, h_v119⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 dropping h_v108 h_v118 hinv116 s116 v108 v118
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__2b.construct s117 e_v120 (by rw [he_v120]; exact empty_args) hinv117 h64 as ⟨v120, s118, hinv118, h_v120⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 dropping he_v120 hinv117 e_v120 s117
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s118 32#u32 (-32) (by scalar_tac) hinv118 h64 as ⟨v121, s119, hinv119, h_v121⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 h_v120 dropping hinv118 s118
  store_step with Store.apply_rep s119 v120 v121 _ _ hinv119 h64 h_v120 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s120, hinv120, h_v122⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 dropping h_v120 h_v121 hinv119 s119 v120 v121
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s120 0#u32 (0) (by scalar_tac) hinv120 h64 as ⟨v123, s121, hinv121, h_v123⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 h_v122 dropping hinv120 s120
  store_step with Store.apply_rep s121 v122 v123 _ _ hinv121 h64 h_v122 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s122, hinv122, h_v124⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 h_v119 dropping h_v122 h_v123 hinv121 s121 v122 v123
  store_step with Store.apply_rep s122 v119 v124 _ _ hinv122 h64 h_v119 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s123, hinv123, h_v125⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v107 dropping h_v119 h_v124 hinv122 s122 v119 v124
  store_step with Store.apply_rep s123 v107 v125 _ _ hinv123 h64 h_v107 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s124, hinv124, h_v126⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping h_v107 h_v125 hinv123 s123 v107 v125
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s124 e_v127 (by rw [he_v127]; exact empty_args) hinv124 h64 as ⟨v127, s125, hinv125, h_v127⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 dropping he_v127 hinv124 e_v127 s124
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s125 e_v128 (by rw [he_v128]; exact empty_args) hinv125 h64 as ⟨v128, s126, hinv126, h_v128⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping he_v128 hinv125 e_v128 s125
  store_step with Store.apply_rep s126 v128 v2 _ _ hinv126 h64 h_v128 h_v2 (by ns_tac) (by ns_tac) as ⟨v129, s127, hinv127, h_v129⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping h_v128 h_v2 hinv126 s126 v128 v2
  step as ⟨e_v130, he_v130⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s127 _ _ rfl hinv127 h64 as ⟨v130, s128, hinv128, h_v130⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v129 dropping hinv127 s127
  replace h_v130 := Represents.rep_of_eq h_v130 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v130]; decide)
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_Int.construct s128 e_v131 (by rw [he_v131]; exact empty_args) hinv128 h64 as ⟨v131, s129, hinv129, h_v131⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v129 h_v130 dropping he_v130 he_v131 hinv128 e_v130 e_v131 s128
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s129 e_v132 (by rw [he_v132]; rfl) h_v130 h_v131 hinv129 h64 as ⟨v132, s130, hinv130, h_v132⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v129 dropping h_v130 h_v131 he_v132 hinv129 e_v132 s129 v130 v131
  store_step with Store.apply_rep s130 v129 v132 _ _ hinv130 h64 h_v129 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s131, hinv131, h_v133⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping h_v129 h_v132 hinv130 s130 v129 v132
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s131 1#u32 (1) (by scalar_tac) hinv131 h64 as ⟨v134, s132, hinv132, h_v134⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 h_v133 dropping hinv131 s131
  store_step with Store.apply_rep s132 v133 v134 _ _ hinv132 h64 h_v133 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s133, hinv133, h_v135⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 h_v127 dropping h_v133 h_v134 hinv132 s132 v133 v134
  store_step with Store.apply_rep s133 v127 v135 _ _ hinv133 h64 h_v127 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s134, hinv134, h_v136⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 h_v126 dropping h_v127 h_v135 hinv133 s133 v127 v135
  store_step with Store.apply_rep s134 v126 v136 _ _ hinv134 h64 h_v126 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s135, hinv135, h_v137⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v70 dropping h_v126 h_v136 hinv134 s134 v126 v136
  store_step with Store.apply_rep s135 v70 v137 _ _ hinv135 h64 h_v70 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s136, hinv136, h_v138⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping h_v137 h_v70 hinv135 s135 v137 v70
  store_step with Store.apply_rep s136 v54 v138 _ _ hinv136 h64 h_v54 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s137, hinv137, h_v139⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 dropping h_v138 h_v54 hinv136 s136 v138 v54
  store_step with Store.literal_boolean_spec s137 false hinv137 h64 as ⟨v140, s138, hinv138, h_v140⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v139 dropping hinv137 s137
  store_step with Store.apply_rep s138 v139 v140 _ _ hinv138 h64 h_v139 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s139, hinv139, h_v141⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 dropping h_v139 h_v140 hinv138 s138 v139 v140
  store_step with Store.apply_rep s139 v53 v141 _ _ hinv139 h64 h_v53 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s140, hinv140, h_v142⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 dropping h_v141 h_v53 hinv139 s139 v141 v53
  store_step with Store.apply_rep s140 v37 v142 _ _ hinv140 h64 h_v37 h_v142 (by ns_tac) (by ns_tac) as ⟨v143, s141, hinv141, h_v143⟩ growing hG carrying h_v16 h_v17 h_v26 dropping h_v142 h_v37 hinv140 s140 v142 v37
  store_step with Store.apply_rep s141 v26 v143 _ _ hinv141 h64 h_v26 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s142, hinv142, h_v144⟩ growing hG carrying h_v16 h_v17 dropping h_v143 h_v26 hinv141 s141 v143 v26
  store_step with Store.apply_rep s142 v17 v144 _ _ hinv142 h64 h_v17 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s143, hinv143, h_v145⟩ growing hG carrying h_v16 dropping h_v144 h_v17 hinv142 s142 v144 v17
  store_step with Store.literal_boolean_spec s143 true hinv143 h64 as ⟨v146, s144, hinv144, h_v146⟩ growing hG carrying h_v16 h_v145 dropping hinv143 s143
  store_step with Store.apply_rep s144 v145 v146 _ _ hinv144 h64 h_v145 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s145, hinv145, h_v147⟩ growing hG carrying h_v16 dropping h_v145 h_v146 hinv144 s144 v145 v146
  store_step with Store.apply_rep s145 v16 v147 _ _ hinv145 h64 h_v16 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s146, hinv146, h_v148⟩ growing hG carrying dropping h_v147 h_v16 hinv145 s145 v147 v16
  case_done hinv146 hG with h_v148 in EoCases.__str_reduction_pred.case_14 using hn_a0 hn_v1 hn_v2

set_option maxHeartbeats 2940000 in
theorem case_15_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_15_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_15 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_15
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2erev.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_15
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  store_step with Store.apply_rep s4 v6 v2 _ _ hinv4 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with Store.apply_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v7 hinv5 s5 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v8 dropping he_v9 hinv6 e_v9 s6
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__40purify.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping he_v10 hinv7 e_v10 s7
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2erev.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 h_v10 dropping he_v11 hinv8 e_v11 s8
  store_step with Store.apply_rep s9 v11 v2 _ _ hinv9 h64 h_v11 h_v2 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 h_v10 dropping h_v11 hinv9 s9 v11
  store_step with Store.apply_rep s10 v10 v12 _ _ hinv10 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping h_v10 h_v12 hinv10 s10 v10 v12
  store_step with Store.apply_rep s11 v9 v13 _ _ hinv11 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v13 h_v9 hinv11 s11 v13 v9
  store_step with Store.apply_rep s12 v8 v14 _ _ hinv12 h64 h_v8 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v4 dropping h_v14 h_v8 hinv12 s12 v14 v8
  store_step with Store.apply_rep s13 v4 v15 _ _ hinv13 h64 h_v4 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 dropping h_v15 h_v4 hinv13 s13 v15 v4
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_and.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v16 dropping he_v17 hinv14 e_v17 s14
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_forall.construct s15 e_v18 (by rw [he_v18]; exact empty_args) hinv15 h64 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v16 h_v17 dropping he_v18 hinv15 e_v18 s15
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s16 e_v19 (by rw [he_v19]; exact empty_args) hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping he_v19 hinv16 e_v19 s16
  step as ⟨e_v20, he_v20⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s17 _ _ rfl hinv17 h64 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 dropping hinv17 s17
  replace h_v20 := Represents.rep_of_eq h_v20 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v20]; decide)
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_Int.construct s18 e_v21 (by rw [he_v21]; exact empty_args) hinv18 h64 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 h_v20 dropping he_v20 he_v21 hinv18 e_v20 e_v21 s18
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s19 e_v22 (by rw [he_v22]; rfl) h_v20 h_v21 hinv19 h64 as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v19 dropping h_v20 h_v21 he_v22 hinv19 e_v22 s19 v20 v21
  store_step with Store.apply_rep s20 v19 v22 _ _ hinv20 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping h_v19 h_v22 hinv20 s20 v19 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s21 e_v24 (by rw [he_v24]; exact empty_args) hinv21 h64 as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 h_v23 dropping he_v24 hinv21 e_v24 s21
  store_step with Store.apply_rep s22 v23 v24 _ _ hinv22 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v2 h_v16 h_v17 h_v18 dropping h_v23 h_v24 hinv22 s22 v23 v24
  store_step with Store.apply_rep s23 v18 v25 _ _ hinv23 h64 h_v18 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_v2 h_v16 h_v17 dropping h_v18 h_v25 hinv23 s23 v18 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_or.construct s24 e_v27 (by rw [he_v27]; exact empty_args) hinv24 h64 as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 dropping he_v27 hinv24 e_v27 s24
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s25 e_v28 (by rw [he_v28]; exact empty_args) hinv25 h64 as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 dropping he_v28 hinv25 e_v28 s25
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3e_3d.construct s26 e_v29 (by rw [he_v29]; exact empty_args) hinv26 h64 as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping he_v29 hinv26 e_v29 s26
  step as ⟨e_v30, he_v30⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s27 _ _ rfl hinv27 h64 as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 dropping hinv27 s27
  replace h_v30 := Represents.rep_of_eq h_v30 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v30]; decide)
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_Int.construct s28 e_v31 (by rw [he_v31]; exact empty_args) hinv28 h64 as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 h_v30 dropping he_v30 he_v31 hinv28 e_v30 e_v31 s28
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s29 e_v32 (by rw [he_v32]; rfl) h_v30 h_v31 hinv29 h64 as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v29 dropping h_v30 h_v31 he_v32 hinv29 e_v32 s29 v30 v31
  store_step with Store.apply_rep s30 v29 v32 _ _ hinv30 h64 h_v29 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping h_v29 h_v32 hinv30 s30 v29 v32
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s31 0#u32 (0) (by scalar_tac) hinv31 h64 as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 h_v33 dropping hinv31 s31
  store_step with Store.apply_rep s32 v33 v34 _ _ hinv32 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 h_v28 dropping h_v33 h_v34 hinv32 s32 v33 v34
  store_step with Store.apply_rep s33 v28 v35 _ _ hinv33 h64 h_v28 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v27 dropping h_v28 h_v35 hinv33 s33 v28 v35
  store_step with Store.apply_rep s34 v27 v36 _ _ hinv34 h64 h_v27 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 dropping h_v27 h_v36 hinv34 s34 v27 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_or.construct s35 e_v38 (by rw [he_v38]; exact empty_args) hinv35 h64 as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 dropping he_v38 hinv35 e_v38 s35
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_not.construct s36 e_v39 (by rw [he_v39]; exact empty_args) hinv36 h64 as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 dropping he_v39 hinv36 e_v39 s36
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3c.construct s37 e_v40 (by rw [he_v40]; exact empty_args) hinv37 h64 as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping he_v40 hinv37 e_v40 s37
  step as ⟨e_v41, he_v41⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s38 _ _ rfl hinv38 h64 as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 dropping hinv38 s38
  replace h_v41 := Represents.rep_of_eq h_v41 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v41]; decide)
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_Int.construct s39 e_v42 (by rw [he_v42]; exact empty_args) hinv39 h64 as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 h_v41 dropping he_v41 he_v42 hinv39 e_v41 e_v42 s39
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s40 e_v43 (by rw [he_v43]; rfl) h_v41 h_v42 hinv40 h64 as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v40 dropping h_v41 h_v42 he_v43 hinv40 e_v43 s40 v41 v42
  store_step with Store.apply_rep s41 v40 v43 _ _ hinv41 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping h_v40 h_v43 hinv41 s41 v40 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_str_2elen.construct s42 e_v45 (by rw [he_v45]; exact empty_args) hinv42 h64 as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 dropping he_v45 hinv42 e_v45 s42
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__40purify.construct s43 e_v46 (by rw [he_v46]; exact empty_args) hinv43 h64 as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 dropping he_v46 hinv43 e_v46 s43
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2erev.construct s44 e_v47 (by rw [he_v47]; exact empty_args) hinv44 h64 as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 h_v46 dropping he_v47 hinv44 e_v47 s44
  store_step with Store.apply_rep s45 v47 v2 _ _ hinv45 h64 h_v47 h_v2 (by ns_tac) (by ns_tac) as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 h_v46 dropping h_v47 hinv45 s45 v47
  store_step with Store.apply_rep s46 v46 v48 _ _ hinv46 h64 h_v46 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 h_v45 dropping h_v46 h_v48 hinv46 s46 v46 v48
  store_step with Store.apply_rep s47 v45 v49 _ _ hinv47 h64 h_v45 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 h_v44 dropping h_v45 h_v49 hinv47 s47 v45 v49
  store_step with Store.apply_rep s48 v44 v50 _ _ hinv48 h64 h_v44 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 h_v39 dropping h_v44 h_v50 hinv48 s48 v44 v50
  store_step with Store.apply_rep s49 v39 v51 _ _ hinv49 h64 h_v39 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v38 dropping h_v39 h_v51 hinv49 s49 v39 v51
  store_step with Store.apply_rep s50 v38 v52 _ _ hinv50 h64 h_v38 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 dropping h_v38 h_v52 hinv50 s50 v38 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_or.construct s51 e_v54 (by rw [he_v54]; exact empty_args) hinv51 h64 as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 dropping he_v54 hinv51 e_v54 s51
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__3d.construct s52 e_v55 (by rw [he_v55]; exact empty_args) hinv52 h64 as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping he_v55 hinv52 e_v55 s52
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s53 e_v56 (by rw [he_v56]; exact empty_args) hinv53 h64 as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping he_v56 hinv53 e_v56 s53
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__40purify.construct s54 e_v57 (by rw [he_v57]; exact empty_args) hinv54 h64 as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping he_v57 hinv54 e_v57 s54
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_str_2erev.construct s55 e_v58 (by rw [he_v58]; exact empty_args) hinv55 h64 as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 dropping he_v58 hinv55 e_v58 s55
  store_step with Store.apply_rep s56 v58 v2 _ _ hinv56 h64 h_v58 h_v2 (by ns_tac) (by ns_tac) as ⟨v59, s57, hinv57, h_v59⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 h_v57 dropping h_v58 hinv56 s56 v58
  store_step with Store.apply_rep s57 v57 v59 _ _ hinv57 h64 h_v57 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s58, hinv58, h_v60⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v56 dropping h_v57 h_v59 hinv57 s57 v57 v59
  store_step with Store.apply_rep s58 v56 v60 _ _ hinv58 h64 h_v56 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s59, hinv59, h_v61⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping h_v56 h_v60 hinv58 s58 v56 v60
  step as ⟨e_v62, he_v62⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s59 _ _ rfl hinv59 h64 as ⟨v62, s60, hinv60, h_v62⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v61 dropping hinv59 s59
  replace h_v62 := Represents.rep_of_eq h_v62 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v62]; decide)
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_Int.construct s60 e_v63 (by rw [he_v63]; exact empty_args) hinv60 h64 as ⟨v63, s61, hinv61, h_v63⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v61 h_v62 dropping he_v62 he_v63 hinv60 e_v62 e_v63 s60
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s61 e_v64 (by rw [he_v64]; rfl) h_v62 h_v63 hinv61 h64 as ⟨v64, s62, hinv62, h_v64⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v61 dropping h_v62 h_v63 he_v64 hinv61 e_v64 s61 v62 v63
  store_step with Store.apply_rep s62 v61 v64 _ _ hinv62 h64 h_v61 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s63, hinv63, h_v65⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping h_v61 h_v64 hinv62 s62 v61 v64
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s63 1#u32 (1) (by scalar_tac) hinv63 h64 as ⟨v66, s64, hinv64, h_v66⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 h_v65 dropping hinv63 s63
  store_step with Store.apply_rep s64 v65 v66 _ _ hinv64 h64 h_v65 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s65, hinv65, h_v67⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v55 dropping h_v65 h_v66 hinv64 s64 v65 v66
  store_step with Store.apply_rep s65 v55 v67 _ _ hinv65 h64 h_v55 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s66, hinv66, h_v68⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping h_v55 h_v67 hinv65 s65 v55 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s66 e_v69 (by rw [he_v69]; exact empty_args) hinv66 h64 as ⟨v69, s67, hinv67, h_v69⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 dropping he_v69 hinv66 e_v69 s66
  store_step with Store.apply_rep s67 v69 v2 _ _ hinv67 h64 h_v69 h_v2 (by ns_tac) (by ns_tac) as ⟨v70, s68, hinv68, h_v70⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 dropping h_v69 hinv67 s67 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo__2d.construct s68 e_v71 (by rw [he_v71]; exact empty_args) hinv68 h64 as ⟨v71, s69, hinv69, h_v71⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 dropping he_v71 hinv68 e_v71 s68
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo_str_2elen.construct s69 e_v72 (by rw [he_v72]; exact empty_args) hinv69 h64 as ⟨v72, s70, hinv70, h_v72⟩ growing hG carrying h_v2 h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v71 dropping he_v72 hinv69 e_v72 s69
  store_step with Store.apply_rep s70 v72 v2 _ _ hinv70 h64 h_v72 h_v2 (by ns_tac) (by ns_tac) as ⟨v73, s71, hinv71, h_v73⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v71 dropping h_v2 h_v72 hinv70 s70 v2 v72
  store_step with Store.apply_rep s71 v71 v73 _ _ hinv71 h64 h_v71 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s72, hinv72, h_v74⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 dropping h_v71 h_v73 hinv71 s71 v71 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo__2b.construct s72 e_v75 (by rw [he_v75]; exact empty_args) hinv72 h64 as ⟨v75, s73, hinv73, h_v75⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 dropping he_v75 hinv72 e_v75 s72
  step as ⟨e_v76, he_v76⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s73 _ _ rfl hinv73 h64 as ⟨v76, s74, hinv74, h_v76⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v75 dropping hinv73 s73
  replace h_v76 := Represents.rep_of_eq h_v76 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v76]; decide)
  step as ⟨e_v77, he_v77⟩
  store_step with CtorSpec.eo_Int.construct s74 e_v77 (by rw [he_v77]; exact empty_args) hinv74 h64 as ⟨v77, s75, hinv75, h_v77⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v75 h_v76 dropping he_v76 he_v77 hinv74 e_v76 e_v77 s74
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s75 e_v78 (by rw [he_v78]; rfl) h_v76 h_v77 hinv75 h64 as ⟨v78, s76, hinv76, h_v78⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v75 dropping h_v76 h_v77 he_v78 hinv75 e_v78 s75 v76 v77
  store_step with Store.apply_rep s76 v75 v78 _ _ hinv76 h64 h_v75 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s77, hinv77, h_v79⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 dropping h_v75 h_v78 hinv76 s76 v75 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo__2b.construct s77 e_v80 (by rw [he_v80]; exact empty_args) hinv77 h64 as ⟨v80, s78, hinv78, h_v80⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v79 dropping he_v80 hinv77 e_v80 s77
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s78 1#u32 (1) (by scalar_tac) hinv78 h64 as ⟨v81, s79, hinv79, h_v81⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v79 h_v80 dropping hinv78 s78
  store_step with Store.apply_rep s79 v80 v81 _ _ hinv79 h64 h_v80 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s80, hinv80, h_v82⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v79 dropping h_v80 h_v81 hinv79 s79 v80 v81
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s80 0#u32 (0) (by scalar_tac) hinv80 h64 as ⟨v83, s81, hinv81, h_v83⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v79 h_v82 dropping hinv80 s80
  store_step with Store.apply_rep s81 v82 v83 _ _ hinv81 h64 h_v82 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s82, hinv82, h_v84⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 h_v79 dropping h_v82 h_v83 hinv81 s81 v82 v83
  store_step with Store.apply_rep s82 v79 v84 _ _ hinv82 h64 h_v79 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s83, hinv83, h_v85⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 h_v74 dropping h_v79 h_v84 hinv82 s82 v79 v84
  store_step with Store.apply_rep s83 v74 v85 _ _ hinv83 h64 h_v74 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s84, hinv84, h_v86⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v70 dropping h_v74 h_v85 hinv83 s83 v74 v85
  store_step with Store.apply_rep s84 v70 v86 _ _ hinv84 h64 h_v70 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s85, hinv85, h_v87⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 dropping h_v70 h_v86 hinv84 s84 v70 v86
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s85 1#u32 (1) (by scalar_tac) hinv85 h64 as ⟨v88, s86, hinv86, h_v88⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 h_v87 dropping hinv85 s85
  store_step with Store.apply_rep s86 v87 v88 _ _ hinv86 h64 h_v87 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s87, hinv87, h_v89⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 h_v68 dropping h_v87 h_v88 hinv86 s86 v87 v88
  store_step with Store.apply_rep s87 v68 v89 _ _ hinv87 h64 h_v68 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s88, hinv88, h_v90⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v54 dropping h_v68 h_v89 hinv87 s87 v68 v89
  store_step with Store.apply_rep s88 v54 v90 _ _ hinv88 h64 h_v54 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s89, hinv89, h_v91⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 dropping h_v54 h_v90 hinv88 s88 v54 v90
  store_step with Store.literal_boolean_spec s89 false hinv89 h64 as ⟨v92, s90, hinv90, h_v92⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 h_v91 dropping hinv89 s89
  store_step with Store.apply_rep s90 v91 v92 _ _ hinv90 h64 h_v91 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s91, hinv91, h_v93⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 h_v53 dropping h_v91 h_v92 hinv90 s90 v91 v92
  store_step with Store.apply_rep s91 v53 v93 _ _ hinv91 h64 h_v53 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s92, hinv92, h_v94⟩ growing hG carrying h_v16 h_v17 h_v26 h_v37 dropping h_v53 h_v93 hinv91 s91 v53 v93
  store_step with Store.apply_rep s92 v37 v94 _ _ hinv92 h64 h_v37 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s93, hinv93, h_v95⟩ growing hG carrying h_v16 h_v17 h_v26 dropping h_v37 h_v94 hinv92 s92 v37 v94
  store_step with Store.apply_rep s93 v26 v95 _ _ hinv93 h64 h_v26 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s94, hinv94, h_v96⟩ growing hG carrying h_v16 h_v17 dropping h_v26 h_v95 hinv93 s93 v26 v95
  store_step with Store.apply_rep s94 v17 v96 _ _ hinv94 h64 h_v17 h_v96 (by ns_tac) (by ns_tac) as ⟨v97, s95, hinv95, h_v97⟩ growing hG carrying h_v16 dropping h_v17 h_v96 hinv94 s94 v17 v96
  store_step with Store.literal_boolean_spec s95 true hinv95 h64 as ⟨v98, s96, hinv96, h_v98⟩ growing hG carrying h_v16 h_v97 dropping hinv95 s95
  store_step with Store.apply_rep s96 v97 v98 _ _ hinv96 h64 h_v97 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s97, hinv97, h_v99⟩ growing hG carrying h_v16 dropping h_v97 h_v98 hinv96 s96 v97 v98
  store_step with Store.apply_rep s97 v16 v99 _ _ hinv97 h64 h_v16 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s98, hinv98, h_v100⟩ growing hG carrying dropping h_v16 h_v99 hinv97 s97 v16 v99
  case_done hinv98 hG with h_v100 in EoCases.__str_reduction_pred.case_15 using hn_a0 hn_v1 hn_v2

theorem cases_0_0_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_0 x_a0 = none ∧ EoCases.__str_reduction_pred.case_1 x_a0 = none ∧ EoCases.__str_reduction_pred.case_2 x_a0 = none ∧ EoCases.__str_reduction_pred.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24str_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] = [] ++ [EoCases.__str_reduction_pred.case_0 x_a0] ++ [EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24str_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] = [EoCases.__str_reduction_pred.case_0 x_a0] ++ [EoCases.__str_reduction_pred.case_1 x_a0] ++ [EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24str_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] = [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0] ++ [EoCases.__str_reduction_pred.case_2 x_a0] ++ [EoCases.__str_reduction_pred.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24str_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] = [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0] ++ [EoCases.__str_reduction_pred.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_4 x_a0 = none ∧ EoCases.__str_reduction_pred.case_5 x_a0 = none ∧ EoCases.__str_reduction_pred.case_6 x_a0 = none ∧ EoCases.__str_reduction_pred.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24str_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] = [] ++ [EoCases.__str_reduction_pred.case_4 x_a0] ++ [EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24str_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] = [EoCases.__str_reduction_pred.case_4 x_a0] ++ [EoCases.__str_reduction_pred.case_5 x_a0] ++ [EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_step with case_6_eo__24str_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] = [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0] ++ [EoCases.__str_reduction_pred.case_6 x_a0] ++ [EoCases.__str_reduction_pred.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hl_4 hl_5
  group_step with case_7_eo__24str_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] = [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0] ++ [EoCases.__str_reduction_pred.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_8 x_a0 = none ∧ EoCases.__str_reduction_pred.case_9 x_a0 = none ∧ EoCases.__str_reduction_pred.case_10 x_a0 = none ∧ EoCases.__str_reduction_pred.case_11 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24str_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] = [] ++ [EoCases.__str_reduction_pred.case_8 x_a0] ++ [EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0
  group_step with case_9_eo__24str_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] = [EoCases.__str_reduction_pred.case_8 x_a0] ++ [EoCases.__str_reduction_pred.case_9 x_a0] ++ [EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hl_8
  group_step with case_10_eo__24str_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] = [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0] ++ [EoCases.__str_reduction_pred.case_10 x_a0] ++ [EoCases.__str_reduction_pred.case_11 x_a0] from rfl)
    otherwise ⟨hl_10⟩ using hn_a0 hl_8 hl_9
  group_step with case_11_eo__24str_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] = [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0] ++ [EoCases.__str_reduction_pred.case_11 x_a0] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hn_a0 hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_3_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_12 x_a0 = none ∧ EoCases.__str_reduction_pred.case_13 x_a0 = none ∧ EoCases.__str_reduction_pred.case_14 x_a0 = none ∧ EoCases.__str_reduction_pred.case_15 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24str_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [] ++ [EoCases.__str_reduction_pred.case_12 x_a0] ++ [EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] from rfl)
    otherwise ⟨hl_12⟩ using hn_a0
  group_step with case_13_eo__24str_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [EoCases.__str_reduction_pred.case_12 x_a0] ++ [EoCases.__str_reduction_pred.case_13 x_a0] ++ [EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] from rfl)
    otherwise ⟨hl_13⟩ using hn_a0 hl_12
  group_step with case_14_eo__24str_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0] ++ [EoCases.__str_reduction_pred.case_14 x_a0] ++ [EoCases.__str_reduction_pred.case_15 x_a0] from rfl)
    otherwise ⟨hl_14⟩ using hn_a0 hl_12 hl_13
  group_step with case_15_eo__24str_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0] ++ [EoCases.__str_reduction_pred.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hn_a0 hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

/-- logos's `__str_reduction_pred` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24str_5freduction_5fpred.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __str_reduction_pred x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __str_reduction_pred
  unfold EoCases.__str_reduction_pred.case_0 EoCases.__str_reduction_pred.case_1 EoCases.__str_reduction_pred.case_2 EoCases.__str_reduction_pred.case_3 EoCases.__str_reduction_pred.case_4 EoCases.__str_reduction_pred.case_5 EoCases.__str_reduction_pred.case_6 EoCases.__str_reduction_pred.case_7 EoCases.__str_reduction_pred.case_8 EoCases.__str_reduction_pred.case_9 EoCases.__str_reduction_pred.case_10 EoCases.__str_reduction_pred.case_11 EoCases.__str_reduction_pred.case_12 EoCases.__str_reduction_pred.case_13 EoCases.__str_reduction_pred.case_14 EoCases.__str_reduction_pred.case_15
  logos_eq

theorem body_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__str_reduction_pred x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24str_5freduction_5fpred.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_0_0_eo__24str_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [] ++ [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] ++ [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  body_group_step with cases_0_1_eo__24str_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0] ++ [EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] ++ [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24str_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0] ++ [EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] ++ [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_group_step with cases_0_3_eo__24str_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0, EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] = [EoCases.__str_reduction_pred.case_0 x_a0, EoCases.__str_reduction_pred.case_1 x_a0, EoCases.__str_reduction_pred.case_2 x_a0, EoCases.__str_reduction_pred.case_3 x_a0, EoCases.__str_reduction_pred.case_4 x_a0, EoCases.__str_reduction_pred.case_5 x_a0, EoCases.__str_reduction_pred.case_6 x_a0, EoCases.__str_reduction_pred.case_7 x_a0, EoCases.__str_reduction_pred.case_8 x_a0, EoCases.__str_reduction_pred.case_9 x_a0, EoCases.__str_reduction_pred.case_10 x_a0, EoCases.__str_reduction_pred.case_11 x_a0] ++ [EoCases.__str_reduction_pred.case_12 x_a0, EoCases.__str_reduction_pred.case_13 x_a0, EoCases.__str_reduction_pred.case_14 x_a0, EoCases.__str_reduction_pred.case_15 x_a0] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  body_stuck hinv4 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 in EoCases.__str_reduction_pred.case_0 EoCases.__str_reduction_pred.case_1 EoCases.__str_reduction_pred.case_2 EoCases.__str_reduction_pred.case_3 EoCases.__str_reduction_pred.case_4 EoCases.__str_reduction_pred.case_5 EoCases.__str_reduction_pred.case_6 EoCases.__str_reduction_pred.case_7 EoCases.__str_reduction_pred.case_8 EoCases.__str_reduction_pred.case_9 EoCases.__str_reduction_pred.case_10 EoCases.__str_reduction_pred.case_11 EoCases.__str_reduction_pred.case_12 EoCases.__str_reduction_pred.case_13 EoCases.__str_reduction_pred.case_14 EoCases.__str_reduction_pred.case_15

theorem eo__24str_5freduction_5fpred_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24str_5freduction_5fpred.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24str_5freduction_5fpred
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24str_5freduction_5fpred s1 a0) (fun s' t => Represents.rep s' t (__str_reduction_pred x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24str_5freduction_5fpred_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
