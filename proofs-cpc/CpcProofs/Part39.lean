module
public import CpcProofs.Head
public import CpcProofs.Part38
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
theorem case_4_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_4
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_4
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3e_3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with Store.apply_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 hinv3 s3 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v6 dropping hinv4 s4
  store_step with Store.apply_rep s5 v6 v7 _ _ hinv5 h64 h_v6 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v6 h_v7 hinv5 s5 v6 v7
  store_step with Store.apply_rep s6 v4 v8 _ _ hinv6 h64 h_v4 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 dropping h_v4 h_v8 hinv6 s6 v4 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_and.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v9 dropping he_v10 hinv7 e_v10 s7
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3e_3d.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v9 h_v10 dropping he_v11 hinv8 e_v11 s8
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v9 h_v10 h_v11 dropping he_v12 hinv9 e_v12 s9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40purify.construct s10 e_v13 (by rw [he_v13]; exact empty_args) hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v9 h_v10 h_v11 h_v12 dropping he_v13 hinv10 e_v13 s10
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s11 e_v14 (by rw [he_v14]; exact empty_args) hinv11 h64 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v9 h_v10 h_v11 h_v12 h_v13 dropping he_v14 hinv11 e_v14 s11
  store_step with Store.apply_rep s12 v14 v2 _ _ hinv12 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v9 h_v10 h_v11 h_v12 h_v13 dropping h_v14 hinv12 s12 v14
  store_step with Store.apply_rep s13 v13 v15 _ _ hinv13 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 h_v9 h_v10 h_v11 h_v12 dropping h_v13 h_v15 hinv13 s13 v13 v15
  store_step with Store.apply_rep s14 v12 v16 _ _ hinv14 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v9 h_v10 h_v11 dropping h_v12 h_v16 hinv14 s14 v12 v16
  store_step with Store.apply_rep s15 v11 v17 _ _ hinv15 h64 h_v11 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v9 h_v10 dropping h_v11 h_v17 hinv15 s15 v11 v17
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 1#u32 (1) (by scalar_tac) hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 h_v9 h_v10 h_v18 dropping hinv16 s16
  store_step with Store.apply_rep s17 v18 v19 _ _ hinv17 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v9 h_v10 dropping h_v18 h_v19 hinv17 s17 v18 v19
  store_step with Store.apply_rep s18 v10 v20 _ _ hinv18 h64 h_v10 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v9 dropping h_v10 h_v20 hinv18 s18 v10 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_and.construct s19 e_v22 (by rw [he_v22]; exact empty_args) hinv19 h64 as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v9 h_v21 dropping he_v22 hinv19 e_v22 s19
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v23 (by rw [he_v23]; exact empty_args) hinv20 h64 as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 dropping he_v23 hinv20 e_v23 s20
  store_step with Store.apply_rep s21 v23 v2 _ _ hinv21 h64 h_v23 h_v2 (by ns_tac) (by ns_tac) as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 dropping h_v23 hinv21 s21 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s22 e_v25 (by rw [he_v25]; exact empty_args) hinv22 h64 as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 dropping he_v25 hinv22 e_v25 s22
  store_step with Store.apply_rep s23 v25 v2 _ _ hinv23 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 dropping h_v25 hinv23 s23 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2elen.construct s24 e_v27 (by rw [he_v27]; exact empty_args) hinv24 h64 as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 h_v26 dropping he_v27 hinv24 e_v27 s24
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__40purify.construct s25 e_v28 (by rw [he_v28]; exact empty_args) hinv25 h64 as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 h_v26 h_v27 dropping he_v28 hinv25 e_v28 s25
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s26 e_v29 (by rw [he_v29]; exact empty_args) hinv26 h64 as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 h_v26 h_v27 h_v28 dropping he_v29 hinv26 e_v29 s26
  store_step with Store.apply_rep s27 v29 v2 _ _ hinv27 h64 h_v29 h_v2 (by ns_tac) (by ns_tac) as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 h_v26 h_v27 h_v28 dropping h_v29 hinv27 s27 v29
  store_step with Store.apply_rep s28 v28 v30 _ _ hinv28 h64 h_v28 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 h_v26 h_v27 dropping h_v28 h_v30 hinv28 s28 v28 v30
  store_step with Store.apply_rep s29 v27 v31 _ _ hinv29 h64 h_v27 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 h_v26 dropping h_v27 h_v31 hinv29 s29 v27 v31
  store_step with Store.apply_rep s30 v26 v32 _ _ hinv30 h64 h_v26 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 h_v24 dropping h_v26 h_v32 hinv30 s30 v26 v32
  store_step with Store.apply_rep s31 v24 v33 _ _ hinv31 h64 h_v24 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_v2 h_v9 h_v21 h_v22 dropping h_v24 h_v33 hinv31 s31 v24 v33
  store_step with Store.apply_rep s32 v22 v34 _ _ hinv32 h64 h_v22 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_v2 h_v9 h_v21 dropping h_v22 h_v34 hinv32 s32 v22 v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_and.construct s33 e_v36 (by rw [he_v36]; exact empty_args) hinv33 h64 as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 dropping he_v36 hinv33 e_v36 s33
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s34 e_v37 (by rw [he_v37]; exact empty_args) hinv34 h64 as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 dropping he_v37 hinv34 e_v37 s34
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s35 0#u32 (0) (by scalar_tac) hinv35 h64 as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 h_v37 dropping hinv35 s35
  store_step with Store.apply_rep s36 v37 v38 _ _ hinv36 h64 h_v37 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 dropping h_v37 h_v38 hinv36 s36 v37 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s37 e_v40 (by rw [he_v40]; exact empty_args) hinv37 h64 as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 h_v39 dropping he_v40 hinv37 e_v40 s37
  store_step with Store.apply_rep s38 v40 v2 _ _ hinv38 h64 h_v40 h_v2 (by ns_tac) (by ns_tac) as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 h_v39 dropping h_v40 hinv38 s38 v40
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s39 0#u32 (0) (by scalar_tac) hinv39 h64 as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 h_v39 h_v41 dropping hinv39 s39
  store_step with Store.apply_rep s40 v41 v42 _ _ hinv40 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 h_v39 dropping h_v41 h_v42 hinv40 s40 v41 v42
  store_step with Store.apply_rep s41 v39 v43 _ _ hinv41 h64 h_v39 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v36 dropping h_v39 h_v43 hinv41 s41 v39 v43
  store_step with Store.apply_rep s42 v36 v44 _ _ hinv42 h64 h_v36 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 dropping h_v36 h_v44 hinv42 s42 v36 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_and.construct s43 e_v46 (by rw [he_v46]; exact empty_args) hinv43 h64 as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 dropping he_v46 hinv43 e_v46 s43
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_forall.construct s44 e_v47 (by rw [he_v47]; exact empty_args) hinv44 h64 as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 dropping he_v47 hinv44 e_v47 s44
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s45 e_v48 (by rw [he_v48]; exact empty_args) hinv45 h64 as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 dropping he_v48 hinv45 e_v48 s45
  step as ⟨e_v49, he_v49⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s46 _ _ rfl hinv46 h64 as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 h_v48 dropping hinv46 s46
  replace h_v49 := Represents.rep_of_eq h_v49 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v49]; decide)
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_Int.construct s47 e_v50 (by rw [he_v50]; exact empty_args) hinv47 h64 as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 h_v48 h_v49 dropping he_v49 he_v50 hinv47 e_v49 e_v50 s47
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s48 e_v51 (by rw [he_v51]; rfl) h_v49 h_v50 hinv48 h64 as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 h_v48 dropping h_v49 h_v50 he_v51 hinv48 e_v51 s48 v49 v50
  store_step with Store.apply_rep s49 v48 v51 _ _ hinv49 h64 h_v48 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 dropping h_v48 h_v51 hinv49 s49 v48 v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s50 e_v53 (by rw [he_v53]; exact empty_args) hinv50 h64 as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 h_v52 dropping he_v53 hinv50 e_v53 s50
  store_step with Store.apply_rep s51 v52 v53 _ _ hinv51 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v47 dropping h_v52 h_v53 hinv51 s51 v52 v53
  store_step with Store.apply_rep s52 v47 v54 _ _ hinv52 h64 h_v47 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 dropping h_v47 h_v54 hinv52 s52 v47 v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_or.construct s53 e_v56 (by rw [he_v56]; exact empty_args) hinv53 h64 as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 dropping he_v56 hinv53 e_v56 s53
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_not.construct s54 e_v57 (by rw [he_v57]; exact empty_args) hinv54 h64 as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 dropping he_v57 hinv54 e_v57 s54
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__3e_3d.construct s55 e_v58 (by rw [he_v58]; exact empty_args) hinv55 h64 as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 dropping he_v58 hinv55 e_v58 s55
  step as ⟨e_v59, he_v59⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s56 _ _ rfl hinv56 h64 as ⟨v59, s57, hinv57, h_v59⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 h_v58 dropping hinv56 s56
  replace h_v59 := Represents.rep_of_eq h_v59 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v59]; decide)
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_Int.construct s57 e_v60 (by rw [he_v60]; exact empty_args) hinv57 h64 as ⟨v60, s58, hinv58, h_v60⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 h_v58 h_v59 dropping he_v59 he_v60 hinv57 e_v59 e_v60 s57
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s58 e_v61 (by rw [he_v61]; rfl) h_v59 h_v60 hinv58 h64 as ⟨v61, s59, hinv59, h_v61⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 h_v58 dropping h_v59 h_v60 he_v61 hinv58 e_v61 s58 v59 v60
  store_step with Store.apply_rep s59 v58 v61 _ _ hinv59 h64 h_v58 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s60, hinv60, h_v62⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 dropping h_v58 h_v61 hinv59 s59 v58 v61
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s60 0#u32 (0) (by scalar_tac) hinv60 h64 as ⟨v63, s61, hinv61, h_v63⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 h_v62 dropping hinv60 s60
  store_step with Store.apply_rep s61 v62 v63 _ _ hinv61 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s62, hinv62, h_v64⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 h_v57 dropping h_v62 h_v63 hinv61 s61 v62 v63
  store_step with Store.apply_rep s62 v57 v64 _ _ hinv62 h64 h_v57 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s63, hinv63, h_v65⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v56 dropping h_v57 h_v64 hinv62 s62 v57 v64
  store_step with Store.apply_rep s63 v56 v65 _ _ hinv63 h64 h_v56 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s64, hinv64, h_v66⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 dropping h_v56 h_v65 hinv63 s63 v56 v65
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_or.construct s64 e_v67 (by rw [he_v67]; exact empty_args) hinv64 h64 as ⟨v67, s65, hinv65, h_v67⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 dropping he_v67 hinv64 e_v67 s64
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo_not.construct s65 e_v68 (by rw [he_v68]; exact empty_args) hinv65 h64 as ⟨v68, s66, hinv66, h_v68⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 dropping he_v68 hinv65 e_v68 s65
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo__3c.construct s66 e_v69 (by rw [he_v69]; exact empty_args) hinv66 h64 as ⟨v69, s67, hinv67, h_v69⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 dropping he_v69 hinv66 e_v69 s66
  step as ⟨e_v70, he_v70⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s67 _ _ rfl hinv67 h64 as ⟨v70, s68, hinv68, h_v70⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v69 dropping hinv67 s67
  replace h_v70 := Represents.rep_of_eq h_v70 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v70]; decide)
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_Int.construct s68 e_v71 (by rw [he_v71]; exact empty_args) hinv68 h64 as ⟨v71, s69, hinv69, h_v71⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v69 h_v70 dropping he_v70 he_v71 hinv68 e_v70 e_v71 s68
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s69 e_v72 (by rw [he_v72]; rfl) h_v70 h_v71 hinv69 h64 as ⟨v72, s70, hinv70, h_v72⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v69 dropping h_v70 h_v71 he_v72 hinv69 e_v72 s69 v70 v71
  store_step with Store.apply_rep s70 v69 v72 _ _ hinv70 h64 h_v69 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s71, hinv71, h_v73⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 dropping h_v69 h_v72 hinv70 s70 v69 v72
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_str_2elen.construct s71 e_v74 (by rw [he_v74]; exact empty_args) hinv71 h64 as ⟨v74, s72, hinv72, h_v74⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v73 dropping he_v74 hinv71 e_v74 s71
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo__40purify.construct s72 e_v75 (by rw [he_v75]; exact empty_args) hinv72 h64 as ⟨v75, s73, hinv73, h_v75⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v73 h_v74 dropping he_v75 hinv72 e_v75 s72
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s73 e_v76 (by rw [he_v76]; exact empty_args) hinv73 h64 as ⟨v76, s74, hinv74, h_v76⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v73 h_v74 h_v75 dropping he_v76 hinv73 e_v76 s73
  store_step with Store.apply_rep s74 v76 v2 _ _ hinv74 h64 h_v76 h_v2 (by ns_tac) (by ns_tac) as ⟨v77, s75, hinv75, h_v77⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v73 h_v74 h_v75 dropping h_v76 hinv74 s74 v76
  store_step with Store.apply_rep s75 v75 v77 _ _ hinv75 h64 h_v75 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s76, hinv76, h_v78⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v73 h_v74 dropping h_v75 h_v77 hinv75 s75 v75 v77
  store_step with Store.apply_rep s76 v74 v78 _ _ hinv76 h64 h_v74 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s77, hinv77, h_v79⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 h_v73 dropping h_v74 h_v78 hinv76 s76 v74 v78
  store_step with Store.apply_rep s77 v73 v79 _ _ hinv77 h64 h_v73 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s78, hinv78, h_v80⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 h_v68 dropping h_v73 h_v79 hinv77 s77 v73 v79
  store_step with Store.apply_rep s78 v68 v80 _ _ hinv78 h64 h_v68 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s79, hinv79, h_v81⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v67 dropping h_v68 h_v80 hinv78 s78 v68 v80
  store_step with Store.apply_rep s79 v67 v81 _ _ hinv79 h64 h_v67 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s80, hinv80, h_v82⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 dropping h_v67 h_v81 hinv79 s79 v67 v81
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_or.construct s80 e_v83 (by rw [he_v83]; exact empty_args) hinv80 h64 as ⟨v83, s81, hinv81, h_v83⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 dropping he_v83 hinv80 e_v83 s80
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_and.construct s81 e_v84 (by rw [he_v84]; exact empty_args) hinv81 h64 as ⟨v84, s82, hinv82, h_v84⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 dropping he_v84 hinv81 e_v84 s81
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo__3d.construct s82 e_v85 (by rw [he_v85]; exact empty_args) hinv82 h64 as ⟨v85, s83, hinv83, h_v85⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 dropping he_v85 hinv82 e_v85 s82
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s83 e_v86 (by rw [he_v86]; exact empty_args) hinv83 h64 as ⟨v86, s84, hinv84, h_v86⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 dropping he_v86 hinv83 e_v86 s83
  store_step with Store.apply_rep s84 v86 v2 _ _ hinv84 h64 h_v86 h_v2 (by ns_tac) (by ns_tac) as ⟨v87, s85, hinv85, h_v87⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 dropping h_v86 hinv84 s84 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo__2b.construct s85 e_v88 (by rw [he_v88]; exact empty_args) hinv85 h64 as ⟨v88, s86, hinv86, h_v88⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 dropping he_v88 hinv85 e_v88 s85
  step as ⟨e_v89, he_v89⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s86 _ _ rfl hinv86 h64 as ⟨v89, s87, hinv87, h_v89⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v88 dropping hinv86 s86
  replace h_v89 := Represents.rep_of_eq h_v89 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v89]; decide)
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_Int.construct s87 e_v90 (by rw [he_v90]; exact empty_args) hinv87 h64 as ⟨v90, s88, hinv88, h_v90⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v88 h_v89 dropping he_v89 he_v90 hinv87 e_v89 e_v90 s87
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s88 e_v91 (by rw [he_v91]; rfl) h_v89 h_v90 hinv88 h64 as ⟨v91, s89, hinv89, h_v91⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v88 dropping h_v89 h_v90 he_v91 hinv88 e_v91 s88 v89 v90
  store_step with Store.apply_rep s89 v88 v91 _ _ hinv89 h64 h_v88 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s90, hinv90, h_v92⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 dropping h_v88 h_v91 hinv89 s89 v88 v91
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo__2b.construct s90 e_v93 (by rw [he_v93]; exact empty_args) hinv90 h64 as ⟨v93, s91, hinv91, h_v93⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v92 dropping he_v93 hinv90 e_v93 s90
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s91 1#u32 (1) (by scalar_tac) hinv91 h64 as ⟨v94, s92, hinv92, h_v94⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v92 h_v93 dropping hinv91 s91
  store_step with Store.apply_rep s92 v93 v94 _ _ hinv92 h64 h_v93 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s93, hinv93, h_v95⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v92 dropping h_v93 h_v94 hinv92 s92 v93 v94
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s93 0#u32 (0) (by scalar_tac) hinv93 h64 as ⟨v96, s94, hinv94, h_v96⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v92 h_v95 dropping hinv93 s93
  store_step with Store.apply_rep s94 v95 v96 _ _ hinv94 h64 h_v95 h_v96 (by ns_tac) (by ns_tac) as ⟨v97, s95, hinv95, h_v97⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 h_v92 dropping h_v95 h_v96 hinv94 s94 v95 v96
  store_step with Store.apply_rep s95 v92 v97 _ _ hinv95 h64 h_v92 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s96, hinv96, h_v98⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 h_v87 dropping h_v92 h_v97 hinv95 s95 v92 v97
  store_step with Store.apply_rep s96 v87 v98 _ _ hinv96 h64 h_v87 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s97, hinv97, h_v99⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v85 dropping h_v87 h_v98 hinv96 s96 v87 v98
  store_step with Store.apply_rep s97 v85 v99 _ _ hinv97 h64 h_v85 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s98, hinv98, h_v100⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 dropping h_v85 h_v99 hinv97 s97 v85 v99
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo__2b.construct s98 e_v101 (by rw [he_v101]; exact empty_args) hinv98 h64 as ⟨v101, s99, hinv99, h_v101⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 dropping he_v101 hinv98 e_v101 s98
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo__2d.construct s99 e_v102 (by rw [he_v102]; exact empty_args) hinv99 h64 as ⟨v102, s100, hinv100, h_v102⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 dropping he_v102 hinv99 e_v102 s99
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s100 e_v103 (by rw [he_v103]; exact empty_args) hinv100 h64 as ⟨v103, s101, hinv101, h_v103⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 dropping he_v103 hinv100 e_v103 s100
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s101 e_v104 (by rw [he_v104]; exact empty_args) hinv101 h64 as ⟨v104, s102, hinv102, h_v104⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 dropping he_v104 hinv101 e_v104 s101
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__40purify.construct s102 e_v105 (by rw [he_v105]; exact empty_args) hinv102 h64 as ⟨v105, s103, hinv103, h_v105⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v104 dropping he_v105 hinv102 e_v105 s102
  step as ⟨e_v106, he_v106⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s103 e_v106 (by rw [he_v106]; exact empty_args) hinv103 h64 as ⟨v106, s104, hinv104, h_v106⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 dropping he_v106 hinv103 e_v106 s103
  store_step with Store.apply_rep s104 v106 v2 _ _ hinv104 h64 h_v106 h_v2 (by ns_tac) (by ns_tac) as ⟨v107, s105, hinv105, h_v107⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 dropping h_v106 hinv104 s104 v106
  store_step with Store.apply_rep s105 v105 v107 _ _ hinv105 h64 h_v105 h_v107 (by ns_tac) (by ns_tac) as ⟨v108, s106, hinv106, h_v108⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v104 dropping h_v105 h_v107 hinv105 s105 v105 v107
  store_step with Store.apply_rep s106 v104 v108 _ _ hinv106 h64 h_v104 h_v108 (by ns_tac) (by ns_tac) as ⟨v109, s107, hinv107, h_v109⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 dropping h_v104 h_v108 hinv106 s106 v104 v108
  step as ⟨e_v110, he_v110⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s107 _ _ rfl hinv107 h64 as ⟨v110, s108, hinv108, h_v110⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v109 dropping hinv107 s107
  replace h_v110 := Represents.rep_of_eq h_v110 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v110]; decide)
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo_Int.construct s108 e_v111 (by rw [he_v111]; exact empty_args) hinv108 h64 as ⟨v111, s109, hinv109, h_v111⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v109 h_v110 dropping he_v110 he_v111 hinv108 e_v110 e_v111 s108
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s109 e_v112 (by rw [he_v112]; rfl) h_v110 h_v111 hinv109 h64 as ⟨v112, s110, hinv110, h_v112⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v109 dropping h_v110 h_v111 he_v112 hinv109 e_v112 s109 v110 v111
  store_step with Store.apply_rep s110 v109 v112 _ _ hinv110 h64 h_v109 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s111, hinv111, h_v113⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 dropping h_v109 h_v112 hinv110 s110 v109 v112
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s111 1#u32 (1) (by scalar_tac) hinv111 h64 as ⟨v114, s112, hinv112, h_v114⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 h_v113 dropping hinv111 s111
  store_step with Store.apply_rep s112 v113 v114 _ _ hinv112 h64 h_v113 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s113, hinv113, h_v115⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 h_v103 dropping h_v113 h_v114 hinv112 s112 v113 v114
  store_step with Store.apply_rep s113 v103 v115 _ _ hinv113 h64 h_v103 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s114, hinv114, h_v116⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v102 dropping h_v103 h_v115 hinv113 s113 v103 v115
  store_step with Store.apply_rep s114 v102 v116 _ _ hinv114 h64 h_v102 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s115, hinv115, h_v117⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 dropping h_v102 h_v116 hinv114 s114 v102 v116
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s115 48#u32 (48) (by scalar_tac) hinv115 h64 as ⟨v118, s116, hinv116, h_v118⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 h_v117 dropping hinv115 s115
  store_step with Store.apply_rep s116 v117 v118 _ _ hinv116 h64 h_v117 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s117, hinv117, h_v119⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v101 dropping h_v117 h_v118 hinv116 s116 v117 v118
  store_step with Store.apply_rep s117 v101 v119 _ _ hinv117 h64 h_v101 h_v119 (by ns_tac) (by ns_tac) as ⟨v120, s118, hinv118, h_v120⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 dropping h_v101 h_v119 hinv117 s117 v101 v119
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo__2b.construct s118 e_v121 (by rw [he_v121]; exact empty_args) hinv118 h64 as ⟨v121, s119, hinv119, h_v121⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 dropping he_v121 hinv118 e_v121 s118
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo__2a.construct s119 e_v122 (by rw [he_v122]; exact empty_args) hinv119 h64 as ⟨v122, s120, hinv120, h_v122⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 dropping he_v122 hinv119 e_v122 s119
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s120 10#u32 (10) (by scalar_tac) hinv120 h64 as ⟨v123, s121, hinv121, h_v123⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v122 dropping hinv120 s120
  store_step with Store.apply_rep s121 v122 v123 _ _ hinv121 h64 h_v122 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s122, hinv122, h_v124⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 dropping h_v122 h_v123 hinv121 s121 v122 v123
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo__2a.construct s122 e_v125 (by rw [he_v125]; exact empty_args) hinv122 h64 as ⟨v125, s123, hinv123, h_v125⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 dropping he_v125 hinv122 e_v125 s122
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s123 e_v126 (by rw [he_v126]; exact empty_args) hinv123 h64 as ⟨v126, s124, hinv124, h_v126⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v125 dropping he_v126 hinv123 e_v126 s123
  store_step with Store.apply_rep s124 v126 v2 _ _ hinv124 h64 h_v126 h_v2 (by ns_tac) (by ns_tac) as ⟨v127, s125, hinv125, h_v127⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v125 dropping h_v126 hinv124 s124 v126
  step as ⟨e_v128, he_v128⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s125 _ _ rfl hinv125 h64 as ⟨v128, s126, hinv126, h_v128⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v125 h_v127 dropping hinv125 s125
  replace h_v128 := Represents.rep_of_eq h_v128 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v128]; decide)
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo_Int.construct s126 e_v129 (by rw [he_v129]; exact empty_args) hinv126 h64 as ⟨v129, s127, hinv127, h_v129⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v125 h_v127 h_v128 dropping he_v128 he_v129 hinv126 e_v128 e_v129 s126
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s127 e_v130 (by rw [he_v130]; rfl) h_v128 h_v129 hinv127 h64 as ⟨v130, s128, hinv128, h_v130⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v125 h_v127 dropping h_v128 h_v129 he_v130 hinv127 e_v130 s127 v128 v129
  store_step with Store.apply_rep s128 v127 v130 _ _ hinv128 h64 h_v127 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s129, hinv129, h_v131⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v125 dropping h_v127 h_v130 hinv128 s128 v127 v130
  store_step with Store.apply_rep s129 v125 v131 _ _ hinv129 h64 h_v125 h_v131 (by ns_tac) (by ns_tac) as ⟨v132, s130, hinv130, h_v132⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 dropping h_v125 h_v131 hinv129 s129 v125 v131
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s130 1#u32 (1) (by scalar_tac) hinv130 h64 as ⟨v133, s131, hinv131, h_v133⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 h_v132 dropping hinv130 s130
  store_step with Store.apply_rep s131 v132 v133 _ _ hinv131 h64 h_v132 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s132, hinv132, h_v134⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 h_v124 dropping h_v132 h_v133 hinv131 s131 v132 v133
  store_step with Store.apply_rep s132 v124 v134 _ _ hinv132 h64 h_v124 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s133, hinv133, h_v135⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v121 dropping h_v124 h_v134 hinv132 s132 v124 v134
  store_step with Store.apply_rep s133 v121 v135 _ _ hinv133 h64 h_v121 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s134, hinv134, h_v136⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 dropping h_v121 h_v135 hinv133 s133 v121 v135
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s134 0#u32 (0) (by scalar_tac) hinv134 h64 as ⟨v137, s135, hinv135, h_v137⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 h_v136 dropping hinv134 s134
  store_step with Store.apply_rep s135 v136 v137 _ _ hinv135 h64 h_v136 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s136, hinv136, h_v138⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 h_v120 dropping h_v136 h_v137 hinv135 s135 v136 v137
  store_step with Store.apply_rep s136 v120 v138 _ _ hinv136 h64 h_v120 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s137, hinv137, h_v139⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 h_v100 dropping h_v120 h_v138 hinv136 s136 v120 v138
  store_step with Store.apply_rep s137 v100 v139 _ _ hinv137 h64 h_v100 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s138, hinv138, h_v140⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v84 dropping h_v100 h_v139 hinv137 s137 v100 v139
  store_step with Store.apply_rep s138 v84 v140 _ _ hinv138 h64 h_v84 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s139, hinv139, h_v141⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 dropping h_v140 h_v84 hinv138 s138 v140 v84
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo_and.construct s139 e_v142 (by rw [he_v142]; exact empty_args) hinv139 h64 as ⟨v142, s140, hinv140, h_v142⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 dropping he_v142 hinv139 e_v142 s139
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_and.construct s140 e_v143 (by rw [he_v143]; exact empty_args) hinv140 h64 as ⟨v143, s141, hinv141, h_v143⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 dropping he_v143 hinv140 e_v143 s140
  step as ⟨e_v144, he_v144⟩
  store_step with CtorSpec.eo__3e_3d.construct s141 e_v144 (by rw [he_v144]; exact empty_args) hinv141 h64 as ⟨v144, s142, hinv142, h_v144⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 dropping he_v144 hinv141 e_v144 s141
  step as ⟨e_v145, he_v145⟩
  store_step with CtorSpec.eo__2d.construct s142 e_v145 (by rw [he_v145]; exact empty_args) hinv142 h64 as ⟨v145, s143, hinv143, h_v145⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 dropping he_v145 hinv142 e_v145 s142
  step as ⟨e_v146, he_v146⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s143 e_v146 (by rw [he_v146]; exact empty_args) hinv143 h64 as ⟨v146, s144, hinv144, h_v146⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 dropping he_v146 hinv143 e_v146 s143
  step as ⟨e_v147, he_v147⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s144 e_v147 (by rw [he_v147]; exact empty_args) hinv144 h64 as ⟨v147, s145, hinv145, h_v147⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 dropping he_v147 hinv144 e_v147 s144
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo__40purify.construct s145 e_v148 (by rw [he_v148]; exact empty_args) hinv145 h64 as ⟨v148, s146, hinv146, h_v148⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v147 dropping he_v148 hinv145 e_v148 s145
  step as ⟨e_v149, he_v149⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s146 e_v149 (by rw [he_v149]; exact empty_args) hinv146 h64 as ⟨v149, s147, hinv147, h_v149⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v147 h_v148 dropping he_v149 hinv146 e_v149 s146
  store_step with Store.apply_rep s147 v149 v2 _ _ hinv147 h64 h_v149 h_v2 (by ns_tac) (by ns_tac) as ⟨v150, s148, hinv148, h_v150⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v147 h_v148 dropping h_v149 hinv147 s147 v149
  store_step with Store.apply_rep s148 v148 v150 _ _ hinv148 h64 h_v148 h_v150 (by ns_tac) (by ns_tac) as ⟨v151, s149, hinv149, h_v151⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v147 dropping h_v148 h_v150 hinv148 s148 v148 v150
  store_step with Store.apply_rep s149 v147 v151 _ _ hinv149 h64 h_v147 h_v151 (by ns_tac) (by ns_tac) as ⟨v152, s150, hinv150, h_v152⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 dropping h_v147 h_v151 hinv149 s149 v147 v151
  step as ⟨e_v153, he_v153⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s150 _ _ rfl hinv150 h64 as ⟨v153, s151, hinv151, h_v153⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v152 dropping hinv150 s150
  replace h_v153 := Represents.rep_of_eq h_v153 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v153]; decide)
  step as ⟨e_v154, he_v154⟩
  store_step with CtorSpec.eo_Int.construct s151 e_v154 (by rw [he_v154]; exact empty_args) hinv151 h64 as ⟨v154, s152, hinv152, h_v154⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v152 h_v153 dropping he_v153 he_v154 hinv151 e_v153 e_v154 s151
  step as ⟨e_v155, he_v155⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s152 e_v155 (by rw [he_v155]; rfl) h_v153 h_v154 hinv152 h64 as ⟨v155, s153, hinv153, h_v155⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v152 dropping h_v153 h_v154 he_v155 hinv152 e_v155 s152 v153 v154
  store_step with Store.apply_rep s153 v152 v155 _ _ hinv153 h64 h_v152 h_v155 (by ns_tac) (by ns_tac) as ⟨v156, s154, hinv154, h_v156⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 dropping h_v152 h_v155 hinv153 s153 v152 v155
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s154 1#u32 (1) (by scalar_tac) hinv154 h64 as ⟨v157, s155, hinv155, h_v157⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v156 dropping hinv154 s154
  store_step with Store.apply_rep s155 v156 v157 _ _ hinv155 h64 h_v156 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s156, hinv156, h_v158⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 dropping h_v156 h_v157 hinv155 s155 v156 v157
  store_step with Store.apply_rep s156 v146 v158 _ _ hinv156 h64 h_v146 h_v158 (by ns_tac) (by ns_tac) as ⟨v159, s157, hinv157, h_v159⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v145 dropping h_v146 h_v158 hinv156 s156 v146 v158
  store_step with Store.apply_rep s157 v145 v159 _ _ hinv157 h64 h_v145 h_v159 (by ns_tac) (by ns_tac) as ⟨v160, s158, hinv158, h_v160⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 dropping h_v145 h_v159 hinv157 s157 v145 v159
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s158 48#u32 (48) (by scalar_tac) hinv158 h64 as ⟨v161, s159, hinv159, h_v161⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 h_v160 dropping hinv158 s158
  store_step with Store.apply_rep s159 v160 v161 _ _ hinv159 h64 h_v160 h_v161 (by ns_tac) (by ns_tac) as ⟨v162, s160, hinv160, h_v162⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v144 dropping h_v160 h_v161 hinv159 s159 v160 v161
  store_step with Store.apply_rep s160 v144 v162 _ _ hinv160 h64 h_v144 h_v162 (by ns_tac) (by ns_tac) as ⟨v163, s161, hinv161, h_v163⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 dropping h_v144 h_v162 hinv160 s160 v144 v162
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo_ite.construct s161 e_v164 (by rw [he_v164]; exact empty_args) hinv161 h64 as ⟨v164, s162, hinv162, h_v164⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 dropping he_v164 hinv161 e_v164 s161
  step as ⟨e_v165, he_v165⟩
  store_step with CtorSpec.eo_and.construct s162 e_v165 (by rw [he_v165]; exact empty_args) hinv162 h64 as ⟨v165, s163, hinv163, h_v165⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 dropping he_v165 hinv162 e_v165 s162
  step as ⟨e_v166, he_v166⟩
  store_step with CtorSpec.eo__3d.construct s163 e_v166 (by rw [he_v166]; exact empty_args) hinv163 h64 as ⟨v166, s164, hinv164, h_v166⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 dropping he_v166 hinv163 e_v166 s163
  step as ⟨e_v167, he_v167⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s164 _ _ rfl hinv164 h64 as ⟨v167, s165, hinv165, h_v167⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 h_v166 dropping hinv164 s164
  replace h_v167 := Represents.rep_of_eq h_v167 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v167]; decide)
  step as ⟨e_v168, he_v168⟩
  store_step with CtorSpec.eo_Int.construct s165 e_v168 (by rw [he_v168]; exact empty_args) hinv165 h64 as ⟨v168, s166, hinv166, h_v168⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 h_v166 h_v167 dropping he_v167 he_v168 hinv165 e_v167 e_v168 s165
  step as ⟨e_v169, he_v169⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s166 e_v169 (by rw [he_v169]; rfl) h_v167 h_v168 hinv166 h64 as ⟨v169, s167, hinv167, h_v169⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 h_v166 dropping h_v167 h_v168 he_v169 hinv166 e_v169 s166 v167 v168
  store_step with Store.apply_rep s167 v166 v169 _ _ hinv167 h64 h_v166 h_v169 (by ns_tac) (by ns_tac) as ⟨v170, s168, hinv168, h_v170⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 dropping h_v166 h_v169 hinv167 s167 v166 v169
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s168 0#u32 (0) (by scalar_tac) hinv168 h64 as ⟨v171, s169, hinv169, h_v171⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 h_v170 dropping hinv168 s168
  store_step with Store.apply_rep s169 v170 v171 _ _ hinv169 h64 h_v170 h_v171 (by ns_tac) (by ns_tac) as ⟨v172, s170, hinv170, h_v172⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v165 dropping h_v170 h_v171 hinv169 s169 v170 v171
  store_step with Store.apply_rep s170 v165 v172 _ _ hinv170 h64 h_v165 h_v172 (by ns_tac) (by ns_tac) as ⟨v173, s171, hinv171, h_v173⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 dropping h_v165 h_v172 hinv170 s170 v165 v172
  step as ⟨e_v174, he_v174⟩
  store_step with CtorSpec.eo_and.construct s171 e_v174 (by rw [he_v174]; exact empty_args) hinv171 h64 as ⟨v174, s172, hinv172, h_v174⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 dropping he_v174 hinv171 e_v174 s171
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo__3e.construct s172 e_v175 (by rw [he_v175]; exact empty_args) hinv172 h64 as ⟨v175, s173, hinv173, h_v175⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 dropping he_v175 hinv172 e_v175 s172
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo_str_2elen.construct s173 e_v176 (by rw [he_v176]; exact empty_args) hinv173 h64 as ⟨v176, s174, hinv174, h_v176⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v175 dropping he_v176 hinv173 e_v176 s173
  step as ⟨e_v177, he_v177⟩
  store_step with CtorSpec.eo__40purify.construct s174 e_v177 (by rw [he_v177]; exact empty_args) hinv174 h64 as ⟨v177, s175, hinv175, h_v177⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v175 h_v176 dropping he_v177 hinv174 e_v177 s174
  step as ⟨e_v178, he_v178⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s175 e_v178 (by rw [he_v178]; exact empty_args) hinv175 h64 as ⟨v178, s176, hinv176, h_v178⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v175 h_v176 h_v177 dropping he_v178 hinv175 e_v178 s175
  store_step with Store.apply_rep s176 v178 v2 _ _ hinv176 h64 h_v178 h_v2 (by ns_tac) (by ns_tac) as ⟨v179, s177, hinv177, h_v179⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v175 h_v176 h_v177 dropping h_v178 hinv176 s176 v178
  store_step with Store.apply_rep s177 v177 v179 _ _ hinv177 h64 h_v177 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s178, hinv178, h_v180⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v175 h_v176 dropping h_v177 h_v179 hinv177 s177 v177 v179
  store_step with Store.apply_rep s178 v176 v180 _ _ hinv178 h64 h_v176 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s179, hinv179, h_v181⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v175 dropping h_v176 h_v180 hinv178 s178 v176 v180
  store_step with Store.apply_rep s179 v175 v181 _ _ hinv179 h64 h_v175 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s180, hinv180, h_v182⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 dropping h_v175 h_v181 hinv179 s179 v175 v181
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s180 1#u32 (1) (by scalar_tac) hinv180 h64 as ⟨v183, s181, hinv181, h_v183⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 h_v182 dropping hinv180 s180
  store_step with Store.apply_rep s181 v182 v183 _ _ hinv181 h64 h_v182 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s182, hinv182, h_v184⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v174 dropping h_v182 h_v183 hinv181 s181 v182 v183
  store_step with Store.apply_rep s182 v174 v184 _ _ hinv182 h64 h_v174 h_v184 (by ns_tac) (by ns_tac) as ⟨v185, s183, hinv183, h_v185⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 dropping h_v174 h_v184 hinv182 s182 v174 v184
  store_step with Store.literal_boolean_spec s183 true hinv183 h64 as ⟨v186, s184, hinv184, h_v186⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 h_v185 dropping hinv183 s183
  store_step with Store.apply_rep s184 v185 v186 _ _ hinv184 h64 h_v185 h_v186 (by ns_tac) (by ns_tac) as ⟨v187, s185, hinv185, h_v187⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 h_v173 dropping h_v185 h_v186 hinv184 s184 v185 v186
  store_step with Store.apply_rep s185 v173 v187 _ _ hinv185 h64 h_v173 h_v187 (by ns_tac) (by ns_tac) as ⟨v188, s186, hinv186, h_v188⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v164 dropping h_v173 h_v187 hinv185 s185 v173 v187
  store_step with Store.apply_rep s186 v164 v188 _ _ hinv186 h64 h_v164 h_v188 (by ns_tac) (by ns_tac) as ⟨v189, s187, hinv187, h_v189⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 dropping h_v164 h_v188 hinv186 s186 v164 v188
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s187 1#u32 (1) (by scalar_tac) hinv187 h64 as ⟨v190, s188, hinv188, h_v190⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v189 dropping hinv187 s187
  store_step with Store.apply_rep s188 v189 v190 _ _ hinv188 h64 h_v189 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s189, hinv189, h_v191⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 dropping h_v189 h_v190 hinv188 s188 v189 v190
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s189 0#u32 (0) (by scalar_tac) hinv189 h64 as ⟨v192, s190, hinv190, h_v192⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 h_v191 dropping hinv189 s189
  store_step with Store.apply_rep s190 v191 v192 _ _ hinv190 h64 h_v191 h_v192 (by ns_tac) (by ns_tac) as ⟨v193, s191, hinv191, h_v193⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 h_v163 dropping h_v191 h_v192 hinv190 s190 v191 v192
  store_step with Store.apply_rep s191 v163 v193 _ _ hinv191 h64 h_v163 h_v193 (by ns_tac) (by ns_tac) as ⟨v194, s192, hinv192, h_v194⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v143 dropping h_v163 h_v193 hinv191 s191 v163 v193
  store_step with Store.apply_rep s192 v143 v194 _ _ hinv192 h64 h_v143 h_v194 (by ns_tac) (by ns_tac) as ⟨v195, s193, hinv193, h_v195⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 dropping h_v143 h_v194 hinv192 s192 v143 v194
  step as ⟨e_v196, he_v196⟩
  store_step with CtorSpec.eo_and.construct s193 e_v196 (by rw [he_v196]; exact empty_args) hinv193 h64 as ⟨v196, s194, hinv194, h_v196⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 dropping he_v196 hinv193 e_v196 s193
  step as ⟨e_v197, he_v197⟩
  store_step with CtorSpec.eo__3c.construct s194 e_v197 (by rw [he_v197]; exact empty_args) hinv194 h64 as ⟨v197, s195, hinv195, h_v197⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 dropping he_v197 hinv194 e_v197 s194
  step as ⟨e_v198, he_v198⟩
  store_step with CtorSpec.eo__2d.construct s195 e_v198 (by rw [he_v198]; exact empty_args) hinv195 h64 as ⟨v198, s196, hinv196, h_v198⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 dropping he_v198 hinv195 e_v198 s195
  step as ⟨e_v199, he_v199⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s196 e_v199 (by rw [he_v199]; exact empty_args) hinv196 h64 as ⟨v199, s197, hinv197, h_v199⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 dropping he_v199 hinv196 e_v199 s196
  step as ⟨e_v200, he_v200⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s197 e_v200 (by rw [he_v200]; exact empty_args) hinv197 h64 as ⟨v200, s198, hinv198, h_v200⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 dropping he_v200 hinv197 e_v200 s197
  step as ⟨e_v201, he_v201⟩
  store_step with CtorSpec.eo__40purify.construct s198 e_v201 (by rw [he_v201]; exact empty_args) hinv198 h64 as ⟨v201, s199, hinv199, h_v201⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v200 dropping he_v201 hinv198 e_v201 s198
  step as ⟨e_v202, he_v202⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s199 e_v202 (by rw [he_v202]; exact empty_args) hinv199 h64 as ⟨v202, s200, hinv200, h_v202⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v200 h_v201 dropping he_v202 hinv199 e_v202 s199
  store_step with Store.apply_rep s200 v202 v2 _ _ hinv200 h64 h_v202 h_v2 (by ns_tac) (by ns_tac) as ⟨v203, s201, hinv201, h_v203⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v200 h_v201 dropping h_v202 hinv200 s200 v202
  store_step with Store.apply_rep s201 v201 v203 _ _ hinv201 h64 h_v201 h_v203 (by ns_tac) (by ns_tac) as ⟨v204, s202, hinv202, h_v204⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v200 dropping h_v201 h_v203 hinv201 s201 v201 v203
  store_step with Store.apply_rep s202 v200 v204 _ _ hinv202 h64 h_v200 h_v204 (by ns_tac) (by ns_tac) as ⟨v205, s203, hinv203, h_v205⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 dropping h_v200 h_v204 hinv202 s202 v200 v204
  step as ⟨e_v206, he_v206⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s203 _ _ rfl hinv203 h64 as ⟨v206, s204, hinv204, h_v206⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v205 dropping hinv203 s203
  replace h_v206 := Represents.rep_of_eq h_v206 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v206]; decide)
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo_Int.construct s204 e_v207 (by rw [he_v207]; exact empty_args) hinv204 h64 as ⟨v207, s205, hinv205, h_v207⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v205 h_v206 dropping he_v206 he_v207 hinv204 e_v206 e_v207 s204
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s205 e_v208 (by rw [he_v208]; rfl) h_v206 h_v207 hinv205 h64 as ⟨v208, s206, hinv206, h_v208⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v205 dropping h_v206 h_v207 he_v208 hinv205 e_v208 s205 v206 v207
  store_step with Store.apply_rep s206 v205 v208 _ _ hinv206 h64 h_v205 h_v208 (by ns_tac) (by ns_tac) as ⟨v209, s207, hinv207, h_v209⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 dropping h_v205 h_v208 hinv206 s206 v205 v208
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s207 1#u32 (1) (by scalar_tac) hinv207 h64 as ⟨v210, s208, hinv208, h_v210⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 h_v209 dropping hinv207 s207
  store_step with Store.apply_rep s208 v209 v210 _ _ hinv208 h64 h_v209 h_v210 (by ns_tac) (by ns_tac) as ⟨v211, s209, hinv209, h_v211⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 h_v199 dropping h_v209 h_v210 hinv208 s208 v209 v210
  store_step with Store.apply_rep s209 v199 v211 _ _ hinv209 h64 h_v199 h_v211 (by ns_tac) (by ns_tac) as ⟨v212, s210, hinv210, h_v212⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v198 dropping h_v199 h_v211 hinv209 s209 v199 v211
  store_step with Store.apply_rep s210 v198 v212 _ _ hinv210 h64 h_v198 h_v212 (by ns_tac) (by ns_tac) as ⟨v213, s211, hinv211, h_v213⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 dropping h_v198 h_v212 hinv210 s210 v198 v212
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s211 48#u32 (48) (by scalar_tac) hinv211 h64 as ⟨v214, s212, hinv212, h_v214⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 h_v213 dropping hinv211 s211
  store_step with Store.apply_rep s212 v213 v214 _ _ hinv212 h64 h_v213 h_v214 (by ns_tac) (by ns_tac) as ⟨v215, s213, hinv213, h_v215⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v197 dropping h_v213 h_v214 hinv212 s212 v213 v214
  store_step with Store.apply_rep s213 v197 v215 _ _ hinv213 h64 h_v197 h_v215 (by ns_tac) (by ns_tac) as ⟨v216, s214, hinv214, h_v216⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 dropping h_v197 h_v215 hinv213 s213 v197 v215
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s214 10#u32 (10) (by scalar_tac) hinv214 h64 as ⟨v217, s215, hinv215, h_v217⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 h_v216 dropping hinv214 s214
  store_step with Store.apply_rep s215 v216 v217 _ _ hinv215 h64 h_v216 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s216, hinv216, h_v218⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v196 dropping h_v216 h_v217 hinv215 s215 v216 v217
  store_step with Store.apply_rep s216 v196 v218 _ _ hinv216 h64 h_v196 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s217, hinv217, h_v219⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 dropping h_v196 h_v218 hinv216 s216 v196 v218
  store_step with Store.literal_boolean_spec s217 true hinv217 h64 as ⟨v220, s218, hinv218, h_v220⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 h_v219 dropping hinv217 s217
  store_step with Store.apply_rep s218 v219 v220 _ _ hinv218 h64 h_v219 h_v220 (by ns_tac) (by ns_tac) as ⟨v221, s219, hinv219, h_v221⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 h_v195 dropping h_v219 h_v220 hinv218 s218 v219 v220
  store_step with Store.apply_rep s219 v195 v221 _ _ hinv219 h64 h_v195 h_v221 (by ns_tac) (by ns_tac) as ⟨v222, s220, hinv220, h_v222⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v142 dropping h_v195 h_v221 hinv219 s219 v195 v221
  store_step with Store.apply_rep s220 v142 v222 _ _ hinv220 h64 h_v142 h_v222 (by ns_tac) (by ns_tac) as ⟨v223, s221, hinv221, h_v223⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 dropping h_v142 h_v222 hinv220 s220 v142 v222
  step as ⟨e_v224, he_v224⟩
  store_step with CtorSpec.eo_and.construct s221 e_v224 (by rw [he_v224]; exact empty_args) hinv221 h64 as ⟨v224, s222, hinv222, h_v224⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 dropping he_v224 hinv221 e_v224 s221
  step as ⟨e_v225, he_v225⟩
  store_step with CtorSpec.eo__3e_3d.construct s222 e_v225 (by rw [he_v225]; exact empty_args) hinv222 h64 as ⟨v225, s223, hinv223, h_v225⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 dropping he_v225 hinv222 e_v225 s222
  store_step with Store.apply_rep s223 v225 v2 _ _ hinv223 h64 h_v225 h_v2 (by ns_tac) (by ns_tac) as ⟨v226, s224, hinv224, h_v226⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 dropping h_v225 hinv223 s223 v225
  step as ⟨e_v227, he_v227⟩
  store_step with CtorSpec.eo__40strings_5fitos_5fresult.construct s224 e_v227 (by rw [he_v227]; exact empty_args) hinv224 h64 as ⟨v227, s225, hinv225, h_v227⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 dropping he_v227 hinv224 e_v227 s224
  store_step with Store.apply_rep s225 v227 v2 _ _ hinv225 h64 h_v227 h_v2 (by ns_tac) (by ns_tac) as ⟨v228, s226, hinv226, h_v228⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 dropping h_v227 hinv225 s225 v227
  step as ⟨e_v229, he_v229⟩
  store_step with CtorSpec.eo__2b.construct s226 e_v229 (by rw [he_v229]; exact empty_args) hinv226 h64 as ⟨v229, s227, hinv227, h_v229⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 dropping he_v229 hinv226 e_v229 s226
  step as ⟨e_v230, he_v230⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s227 _ _ rfl hinv227 h64 as ⟨v230, s228, hinv228, h_v230⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v229 dropping hinv227 s227
  replace h_v230 := Represents.rep_of_eq h_v230 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v230]; decide)
  step as ⟨e_v231, he_v231⟩
  store_step with CtorSpec.eo_Int.construct s228 e_v231 (by rw [he_v231]; exact empty_args) hinv228 h64 as ⟨v231, s229, hinv229, h_v231⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v229 h_v230 dropping he_v230 he_v231 hinv228 e_v230 e_v231 s228
  step as ⟨e_v232, he_v232⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s229 e_v232 (by rw [he_v232]; rfl) h_v230 h_v231 hinv229 h64 as ⟨v232, s230, hinv230, h_v232⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v229 dropping h_v230 h_v231 he_v232 hinv229 e_v232 s229 v230 v231
  store_step with Store.apply_rep s230 v229 v232 _ _ hinv230 h64 h_v229 h_v232 (by ns_tac) (by ns_tac) as ⟨v233, s231, hinv231, h_v233⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 dropping h_v229 h_v232 hinv230 s230 v229 v232
  step as ⟨e_v234, he_v234⟩
  store_step with CtorSpec.eo__2b.construct s231 e_v234 (by rw [he_v234]; exact empty_args) hinv231 h64 as ⟨v234, s232, hinv232, h_v234⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v233 dropping he_v234 hinv231 e_v234 s231
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s232 1#u32 (1) (by scalar_tac) hinv232 h64 as ⟨v235, s233, hinv233, h_v235⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v233 h_v234 dropping hinv232 s232
  store_step with Store.apply_rep s233 v234 v235 _ _ hinv233 h64 h_v234 h_v235 (by ns_tac) (by ns_tac) as ⟨v236, s234, hinv234, h_v236⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v233 dropping h_v234 h_v235 hinv233 s233 v234 v235
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s234 0#u32 (0) (by scalar_tac) hinv234 h64 as ⟨v237, s235, hinv235, h_v237⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v233 h_v236 dropping hinv234 s234
  store_step with Store.apply_rep s235 v236 v237 _ _ hinv235 h64 h_v236 h_v237 (by ns_tac) (by ns_tac) as ⟨v238, s236, hinv236, h_v238⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 h_v233 dropping h_v236 h_v237 hinv235 s235 v236 v237
  store_step with Store.apply_rep s236 v233 v238 _ _ hinv236 h64 h_v233 h_v238 (by ns_tac) (by ns_tac) as ⟨v239, s237, hinv237, h_v239⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 h_v228 dropping h_v233 h_v238 hinv236 s236 v233 v238
  store_step with Store.apply_rep s237 v228 v239 _ _ hinv237 h64 h_v228 h_v239 (by ns_tac) (by ns_tac) as ⟨v240, s238, hinv238, h_v240⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 h_v226 dropping h_v228 h_v239 hinv237 s237 v228 v239
  store_step with Store.apply_rep s238 v226 v240 _ _ hinv238 h64 h_v226 h_v240 (by ns_tac) (by ns_tac) as ⟨v241, s239, hinv239, h_v241⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v224 dropping h_v226 h_v240 hinv238 s238 v226 v240
  store_step with Store.apply_rep s239 v224 v241 _ _ hinv239 h64 h_v224 h_v241 (by ns_tac) (by ns_tac) as ⟨v242, s240, hinv240, h_v242⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 dropping h_v224 h_v241 hinv239 s239 v224 v241
  store_step with Store.literal_boolean_spec s240 true hinv240 h64 as ⟨v243, s241, hinv241, h_v243⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 h_v242 dropping hinv240 s240
  store_step with Store.apply_rep s241 v242 v243 _ _ hinv241 h64 h_v242 h_v243 (by ns_tac) (by ns_tac) as ⟨v244, s242, hinv242, h_v244⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 h_v223 dropping h_v242 h_v243 hinv241 s241 v242 v243
  store_step with Store.apply_rep s242 v223 v244 _ _ hinv242 h64 h_v223 h_v244 (by ns_tac) (by ns_tac) as ⟨v245, s243, hinv243, h_v245⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 h_v141 dropping h_v223 h_v244 hinv242 s242 v223 v244
  store_step with Store.apply_rep s243 v141 v245 _ _ hinv243 h64 h_v141 h_v245 (by ns_tac) (by ns_tac) as ⟨v246, s244, hinv244, h_v246⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v83 dropping h_v141 h_v245 hinv243 s243 v141 v245
  store_step with Store.apply_rep s244 v83 v246 _ _ hinv244 h64 h_v83 h_v246 (by ns_tac) (by ns_tac) as ⟨v247, s245, hinv245, h_v247⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 dropping h_v246 h_v83 hinv244 s244 v246 v83
  store_step with Store.literal_boolean_spec s245 false hinv245 h64 as ⟨v248, s246, hinv246, h_v248⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 h_v247 dropping hinv245 s245
  store_step with Store.apply_rep s246 v247 v248 _ _ hinv246 h64 h_v247 h_v248 (by ns_tac) (by ns_tac) as ⟨v249, s247, hinv247, h_v249⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 h_v82 dropping h_v247 h_v248 hinv246 s246 v247 v248
  store_step with Store.apply_rep s247 v82 v249 _ _ hinv247 h64 h_v82 h_v249 (by ns_tac) (by ns_tac) as ⟨v250, s248, hinv248, h_v250⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 h_v66 dropping h_v249 h_v82 hinv247 s247 v249 v82
  store_step with Store.apply_rep s248 v66 v250 _ _ hinv248 h64 h_v66 h_v250 (by ns_tac) (by ns_tac) as ⟨v251, s249, hinv249, h_v251⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 h_v55 dropping h_v250 h_v66 hinv248 s248 v250 v66
  store_step with Store.apply_rep s249 v55 v251 _ _ hinv249 h64 h_v55 h_v251 (by ns_tac) (by ns_tac) as ⟨v252, s250, hinv250, h_v252⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v46 dropping h_v251 h_v55 hinv249 s249 v251 v55
  store_step with Store.apply_rep s250 v46 v252 _ _ hinv250 h64 h_v46 h_v252 (by ns_tac) (by ns_tac) as ⟨v253, s251, hinv251, h_v253⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 dropping h_v252 h_v46 hinv250 s250 v252 v46
  store_step with Store.literal_boolean_spec s251 true hinv251 h64 as ⟨v254, s252, hinv252, h_v254⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 h_v253 dropping hinv251 s251
  store_step with Store.apply_rep s252 v253 v254 _ _ hinv252 h64 h_v253 h_v254 (by ns_tac) (by ns_tac) as ⟨v255, s253, hinv253, h_v255⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 h_v45 dropping h_v253 h_v254 hinv252 s252 v253 v254
  store_step with Store.apply_rep s253 v45 v255 _ _ hinv253 h64 h_v45 h_v255 (by ns_tac) (by ns_tac) as ⟨v256, s254, hinv254, h_v256⟩ growing hG carrying h_v2 h_v9 h_v21 h_v35 dropping h_v255 h_v45 hinv253 s253 v255 v45
  store_step with Store.apply_rep s254 v35 v256 _ _ hinv254 h64 h_v35 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s255, hinv255, h_v257⟩ growing hG carrying h_v2 h_v9 h_v21 dropping h_v256 h_v35 hinv254 s254 v256 v35
  store_step with Store.apply_rep s255 v21 v257 _ _ hinv255 h64 h_v21 h_v257 (by ns_tac) (by ns_tac) as ⟨v258, s256, hinv256, h_v258⟩ growing hG carrying h_v2 h_v9 dropping h_v21 h_v257 hinv255 s255 v21 v257
  store_step with Store.apply_rep s256 v9 v258 _ _ hinv256 h64 h_v9 h_v258 (by ns_tac) (by ns_tac) as ⟨v259, s257, hinv257, h_v259⟩ growing hG carrying h_v2 dropping h_v258 h_v9 hinv256 s256 v258 v9
  step as ⟨e_v260, he_v260⟩
  store_step with CtorSpec.eo__3d.construct s257 e_v260 (by rw [he_v260]; exact empty_args) hinv257 h64 as ⟨v260, s258, hinv258, h_v260⟩ growing hG carrying h_v2 h_v259 dropping he_v260 hinv257 e_v260 s257
  step as ⟨e_v261, he_v261⟩
  store_step with CtorSpec.eo__40purify.construct s258 e_v261 (by rw [he_v261]; exact empty_args) hinv258 h64 as ⟨v261, s259, hinv259, h_v261⟩ growing hG carrying h_v2 h_v259 h_v260 dropping he_v261 hinv258 e_v261 s258
  step as ⟨e_v262, he_v262⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s259 e_v262 (by rw [he_v262]; exact empty_args) hinv259 h64 as ⟨v262, s260, hinv260, h_v262⟩ growing hG carrying h_v2 h_v259 h_v260 h_v261 dropping he_v262 hinv259 e_v262 s259
  store_step with Store.apply_rep s260 v262 v2 _ _ hinv260 h64 h_v262 h_v2 (by ns_tac) (by ns_tac) as ⟨v263, s261, hinv261, h_v263⟩ growing hG carrying h_v259 h_v260 h_v261 dropping h_v2 h_v262 hinv260 s260 v2 v262
  store_step with Store.apply_rep s261 v261 v263 _ _ hinv261 h64 h_v261 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s262, hinv262, h_v264⟩ growing hG carrying h_v259 h_v260 dropping h_v261 h_v263 hinv261 s261 v261 v263
  store_step with Store.apply_rep s262 v260 v264 _ _ hinv262 h64 h_v260 h_v264 (by ns_tac) (by ns_tac) as ⟨v265, s263, hinv263, h_v265⟩ growing hG carrying h_v259 dropping h_v260 h_v264 hinv262 s262 v260 v264
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s263 _ _ rfl hinv263 h64 as ⟨v266, s264, hinv264, h_v266⟩ growing hG carrying h_v259 h_v265 dropping hinv263 s263
  store_step with Store.apply_rep s264 v265 v266 _ _ hinv264 h64 h_v265 h_v266 (by ns_tac) (by ns_tac) as ⟨v267, s265, hinv265, h_v267⟩ growing hG carrying h_v259 dropping h_v265 h_v266 hinv264 s264 v265 v266
  store_step with Store.apply_rep s265 v259 v267 _ _ hinv265 h64 h_v259 h_v267 (by ns_tac) (by ns_tac) as ⟨v268, s266, hinv266, h_v268⟩ growing hG carrying dropping h_v259 h_v267 hinv265 s265 v259 v267
  case_done hinv266 hG with h_v268 in EoCases.__str_reduction_pred.case_4 using hn_a0 hn_v1 hn_v2

set_option maxHeartbeats 9210000 in
theorem case_5_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_5
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_5
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40purify.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s4 e_v7 (by rw [he_v7]; exact empty_args) hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 dropping he_v7 hinv4 e_v7 s4
  store_step with Store.apply_rep s5 v7 v2 _ _ hinv5 h64 h_v7 h_v2 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 h_v5 h_v6 dropping h_v7 hinv5 s5 v7
  store_step with Store.apply_rep s6 v6 v8 _ _ hinv6 h64 h_v6 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 h_v8 hinv6 s6 v6 v8
  store_step with Store.apply_rep s7 v5 v9 _ _ hinv7 h64 h_v5 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v9 hinv7 s7 v5 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v10 dropping hinv8 s8
  store_step with Store.apply_rep s9 v10 v11 _ _ hinv9 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 dropping h_v10 h_v11 hinv9 s9 v10 v11
  store_step with Store.apply_rep s10 v4 v12 _ _ hinv10 h64 h_v4 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 dropping h_v12 h_v4 hinv10 s10 v12 v4
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s11 e_v14 (by rw [he_v14]; exact empty_args) hinv11 h64 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v13 dropping he_v14 hinv11 e_v14 s11
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v15 (by rw [he_v15]; exact empty_args) hinv12 h64 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v13 h_v14 dropping he_v15 hinv12 e_v15 s12
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__40purify.construct s13 e_v16 (by rw [he_v16]; exact empty_args) hinv13 h64 as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 h_v13 h_v14 h_v15 dropping he_v16 hinv13 e_v16 s13
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v13 h_v14 h_v15 h_v16 dropping he_v17 hinv14 e_v17 s14
  store_step with Store.apply_rep s15 v17 v2 _ _ hinv15 h64 h_v17 h_v2 (by ns_tac) (by ns_tac) as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v13 h_v14 h_v15 h_v16 dropping h_v17 hinv15 s15 v17
  store_step with Store.apply_rep s16 v16 v18 _ _ hinv16 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 h_v13 h_v14 h_v15 dropping h_v16 h_v18 hinv16 s16 v16 v18
  store_step with Store.apply_rep s17 v15 v19 _ _ hinv17 h64 h_v15 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v13 h_v14 dropping h_v15 h_v19 hinv17 s17 v15 v19
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s18 1#u32 (-1) (by scalar_tac) hinv18 h64 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v13 h_v14 h_v20 dropping hinv18 s18
  store_step with Store.apply_rep s19 v20 v21 _ _ hinv19 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v13 h_v14 dropping h_v20 h_v21 hinv19 s19 v20 v21
  store_step with Store.apply_rep s20 v14 v22 _ _ hinv20 h64 h_v14 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v2 h_v13 dropping h_v14 h_v22 hinv20 s20 v14 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_and.construct s21 e_v24 (by rw [he_v24]; exact empty_args) hinv21 h64 as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v2 h_v13 h_v23 dropping he_v24 hinv21 e_v24 s21
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_or.construct s22 e_v25 (by rw [he_v25]; exact empty_args) hinv22 h64 as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 dropping he_v25 hinv22 e_v25 s22
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v26 (by rw [he_v26]; exact empty_args) hinv23 h64 as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v25 dropping he_v26 hinv23 e_v26 s23
  store_step with Store.apply_rep s24 v26 v2 _ _ hinv24 h64 h_v26 h_v2 (by ns_tac) (by ns_tac) as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v25 dropping h_v26 hinv24 s24 v26
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s25 _ _ rfl hinv25 h64 as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v25 h_v27 dropping hinv25 s25
  store_step with Store.apply_rep s26 v27 v28 _ _ hinv26 h64 h_v27 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v25 dropping h_v27 h_v28 hinv26 s26 v27 v28
  store_step with Store.apply_rep s27 v25 v29 _ _ hinv27 h64 h_v25 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 dropping h_v25 h_v29 hinv27 s27 v25 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_or.construct s28 e_v31 (by rw [he_v31]; exact empty_args) hinv28 h64 as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 dropping he_v31 hinv28 e_v31 s28
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_and.construct s29 e_v32 (by rw [he_v32]; exact empty_args) hinv29 h64 as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 dropping he_v32 hinv29 e_v32 s29
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s30 e_v33 (by rw [he_v33]; exact empty_args) hinv30 h64 as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v32 dropping he_v33 hinv30 e_v33 s30
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct s31 e_v34 (by rw [he_v34]; exact empty_args) hinv31 h64 as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v32 h_v33 dropping he_v34 hinv31 e_v34 s31
  store_step with Store.apply_rep s32 v34 v2 _ _ hinv32 h64 h_v34 h_v2 (by ns_tac) (by ns_tac) as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v32 h_v33 dropping h_v34 hinv32 s32 v34
  store_step with Store.apply_rep s33 v33 v35 _ _ hinv33 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v32 dropping h_v33 h_v35 hinv33 s33 v33 v35
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s34 0#u32 (0) (by scalar_tac) hinv34 h64 as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v32 h_v36 dropping hinv34 s34
  store_step with Store.apply_rep s35 v36 v37 _ _ hinv35 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v32 dropping h_v36 h_v37 hinv35 s35 v36 v37
  store_step with Store.apply_rep s36 v32 v38 _ _ hinv36 h64 h_v32 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 dropping h_v32 h_v38 hinv36 s36 v32 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_and.construct s37 e_v40 (by rw [he_v40]; exact empty_args) hinv37 h64 as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 dropping he_v40 hinv37 e_v40 s37
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3c.construct s38 e_v41 (by rw [he_v41]; exact empty_args) hinv38 h64 as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 dropping he_v41 hinv38 e_v41 s38
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct s39 e_v42 (by rw [he_v42]; exact empty_args) hinv39 h64 as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 h_v41 dropping he_v42 hinv39 e_v42 s39
  store_step with Store.apply_rep s40 v42 v2 _ _ hinv40 h64 h_v42 h_v2 (by ns_tac) (by ns_tac) as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 h_v41 dropping h_v42 hinv40 s40 v42
  store_step with Store.apply_rep s41 v41 v43 _ _ hinv41 h64 h_v41 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 dropping h_v41 h_v43 hinv41 s41 v41 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_str_2elen.construct s42 e_v45 (by rw [he_v45]; exact empty_args) hinv42 h64 as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 h_v44 dropping he_v45 hinv42 e_v45 s42
  store_step with Store.apply_rep s43 v45 v2 _ _ hinv43 h64 h_v45 h_v2 (by ns_tac) (by ns_tac) as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 h_v44 dropping h_v45 hinv43 s43 v45
  store_step with Store.apply_rep s44 v44 v46 _ _ hinv44 h64 h_v44 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v40 dropping h_v44 h_v46 hinv44 s44 v44 v46
  store_step with Store.apply_rep s45 v40 v47 _ _ hinv45 h64 h_v40 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 dropping h_v40 h_v47 hinv45 s45 v40 v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_and.construct s46 e_v49 (by rw [he_v49]; exact empty_args) hinv46 h64 as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 dropping he_v49 hinv46 e_v49 s46
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_or.construct s47 e_v50 (by rw [he_v50]; exact empty_args) hinv47 h64 as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 dropping he_v50 hinv47 e_v50 s47
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3c.construct s48 e_v51 (by rw [he_v51]; exact empty_args) hinv48 h64 as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 dropping he_v51 hinv48 e_v51 s48
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__2d.construct s49 e_v52 (by rw [he_v52]; exact empty_args) hinv49 h64 as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 dropping he_v52 hinv49 e_v52 s49
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s50 e_v53 (by rw [he_v53]; exact empty_args) hinv50 h64 as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 dropping he_v53 hinv50 e_v53 s50
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s51 e_v54 (by rw [he_v54]; exact empty_args) hinv51 h64 as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 dropping he_v54 hinv51 e_v54 s51
  store_step with Store.apply_rep s52 v54 v2 _ _ hinv52 h64 h_v54 h_v2 (by ns_tac) (by ns_tac) as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 dropping h_v54 hinv52 s52 v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct s53 e_v56 (by rw [he_v56]; exact empty_args) hinv53 h64 as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v55 dropping he_v56 hinv53 e_v56 s53
  store_step with Store.apply_rep s54 v56 v2 _ _ hinv54 h64 h_v56 h_v2 (by ns_tac) (by ns_tac) as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v55 dropping h_v56 hinv54 s54 v56
  store_step with Store.apply_rep s55 v55 v57 _ _ hinv55 h64 h_v55 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 dropping h_v55 h_v57 hinv55 s55 v55 v57
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s56 1#u32 (1) (by scalar_tac) hinv56 h64 as ⟨v59, s57, hinv57, h_v59⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v58 dropping hinv56 s56
  store_step with Store.apply_rep s57 v58 v59 _ _ hinv57 h64 h_v58 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s58, hinv58, h_v60⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 dropping h_v58 h_v59 hinv57 s57 v58 v59
  store_step with Store.apply_rep s58 v53 v60 _ _ hinv58 h64 h_v53 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s59, hinv59, h_v61⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v52 dropping h_v53 h_v60 hinv58 s58 v53 v60
  store_step with Store.apply_rep s59 v52 v61 _ _ hinv59 h64 h_v52 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s60, hinv60, h_v62⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 dropping h_v52 h_v61 hinv59 s59 v52 v61
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s60 48#u32 (48) (by scalar_tac) hinv60 h64 as ⟨v63, s61, hinv61, h_v63⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 h_v62 dropping hinv60 s60
  store_step with Store.apply_rep s61 v62 v63 _ _ hinv61 h64 h_v62 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s62, hinv62, h_v64⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v51 dropping h_v62 h_v63 hinv61 s61 v62 v63
  store_step with Store.apply_rep s62 v51 v64 _ _ hinv62 h64 h_v51 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s63, hinv63, h_v65⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 dropping h_v51 h_v64 hinv62 s62 v51 v64
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s63 0#u32 (0) (by scalar_tac) hinv63 h64 as ⟨v66, s64, hinv64, h_v66⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 h_v65 dropping hinv63 s63
  store_step with Store.apply_rep s64 v65 v66 _ _ hinv64 h64 h_v65 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s65, hinv65, h_v67⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v50 dropping h_v65 h_v66 hinv64 s64 v65 v66
  store_step with Store.apply_rep s65 v50 v67 _ _ hinv65 h64 h_v50 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s66, hinv66, h_v68⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 dropping h_v50 h_v67 hinv65 s65 v50 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_or.construct s66 e_v69 (by rw [he_v69]; exact empty_args) hinv66 h64 as ⟨v69, s67, hinv67, h_v69⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 dropping he_v69 hinv66 e_v69 s66
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo__3e_3d.construct s67 e_v70 (by rw [he_v70]; exact empty_args) hinv67 h64 as ⟨v70, s68, hinv68, h_v70⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 dropping he_v70 hinv67 e_v70 s67
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo__2d.construct s68 e_v71 (by rw [he_v71]; exact empty_args) hinv68 h64 as ⟨v71, s69, hinv69, h_v71⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 dropping he_v71 hinv68 e_v71 s68
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s69 e_v72 (by rw [he_v72]; exact empty_args) hinv69 h64 as ⟨v72, s70, hinv70, h_v72⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 dropping he_v72 hinv69 e_v72 s69
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s70 e_v73 (by rw [he_v73]; exact empty_args) hinv70 h64 as ⟨v73, s71, hinv71, h_v73⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 dropping he_v73 hinv70 e_v73 s70
  store_step with Store.apply_rep s71 v73 v2 _ _ hinv71 h64 h_v73 h_v2 (by ns_tac) (by ns_tac) as ⟨v74, s72, hinv72, h_v74⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 dropping h_v73 hinv71 s71 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct s72 e_v75 (by rw [he_v75]; exact empty_args) hinv72 h64 as ⟨v75, s73, hinv73, h_v75⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 h_v74 dropping he_v75 hinv72 e_v75 s72
  store_step with Store.apply_rep s73 v75 v2 _ _ hinv73 h64 h_v75 h_v2 (by ns_tac) (by ns_tac) as ⟨v76, s74, hinv74, h_v76⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 h_v74 dropping h_v75 hinv73 s73 v75
  store_step with Store.apply_rep s74 v74 v76 _ _ hinv74 h64 h_v74 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s75, hinv75, h_v77⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 dropping h_v74 h_v76 hinv74 s74 v74 v76
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s75 1#u32 (1) (by scalar_tac) hinv75 h64 as ⟨v78, s76, hinv76, h_v78⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 h_v77 dropping hinv75 s75
  store_step with Store.apply_rep s76 v77 v78 _ _ hinv76 h64 h_v77 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s77, hinv77, h_v79⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 h_v72 dropping h_v77 h_v78 hinv76 s76 v77 v78
  store_step with Store.apply_rep s77 v72 v79 _ _ hinv77 h64 h_v72 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s78, hinv78, h_v80⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v71 dropping h_v72 h_v79 hinv77 s77 v72 v79
  store_step with Store.apply_rep s78 v71 v80 _ _ hinv78 h64 h_v71 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s79, hinv79, h_v81⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 dropping h_v71 h_v80 hinv78 s78 v71 v80
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s79 48#u32 (48) (by scalar_tac) hinv79 h64 as ⟨v82, s80, hinv80, h_v82⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 h_v81 dropping hinv79 s79
  store_step with Store.apply_rep s80 v81 v82 _ _ hinv80 h64 h_v81 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s81, hinv81, h_v83⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v70 dropping h_v81 h_v82 hinv80 s80 v81 v82
  store_step with Store.apply_rep s81 v70 v83 _ _ hinv81 h64 h_v70 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s82, hinv82, h_v84⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 dropping h_v70 h_v83 hinv81 s81 v70 v83
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s82 10#u32 (10) (by scalar_tac) hinv82 h64 as ⟨v85, s83, hinv83, h_v85⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 h_v84 dropping hinv82 s82
  store_step with Store.apply_rep s83 v84 v85 _ _ hinv83 h64 h_v84 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s84, hinv84, h_v86⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v69 dropping h_v84 h_v85 hinv83 s83 v84 v85
  store_step with Store.apply_rep s84 v69 v86 _ _ hinv84 h64 h_v69 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s85, hinv85, h_v87⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 dropping h_v69 h_v86 hinv84 s84 v69 v86
  store_step with Store.literal_boolean_spec s85 false hinv85 h64 as ⟨v88, s86, hinv86, h_v88⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 h_v87 dropping hinv85 s85
  store_step with Store.apply_rep s86 v87 v88 _ _ hinv86 h64 h_v87 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s87, hinv87, h_v89⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 h_v68 dropping h_v87 h_v88 hinv86 s86 v87 v88
  store_step with Store.apply_rep s87 v68 v89 _ _ hinv87 h64 h_v68 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s88, hinv88, h_v90⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v49 dropping h_v68 h_v89 hinv87 s87 v68 v89
  store_step with Store.apply_rep s88 v49 v90 _ _ hinv88 h64 h_v49 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s89, hinv89, h_v91⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 dropping h_v49 h_v90 hinv88 s88 v49 v90
  store_step with Store.literal_boolean_spec s89 true hinv89 h64 as ⟨v92, s90, hinv90, h_v92⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 h_v91 dropping hinv89 s89
  store_step with Store.apply_rep s90 v91 v92 _ _ hinv90 h64 h_v91 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s91, hinv91, h_v93⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 h_v48 dropping h_v91 h_v92 hinv90 s90 v91 v92
  store_step with Store.apply_rep s91 v48 v93 _ _ hinv91 h64 h_v48 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s92, hinv92, h_v94⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 h_v39 dropping h_v48 h_v93 hinv91 s91 v48 v93
  store_step with Store.apply_rep s92 v39 v94 _ _ hinv92 h64 h_v39 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s93, hinv93, h_v95⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v31 dropping h_v39 h_v94 hinv92 s92 v39 v94
  store_step with Store.apply_rep s93 v31 v95 _ _ hinv93 h64 h_v31 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s94, hinv94, h_v96⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 dropping h_v31 h_v95 hinv93 s93 v31 v95
  store_step with Store.literal_boolean_spec s94 false hinv94 h64 as ⟨v97, s95, hinv95, h_v97⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 h_v96 dropping hinv94 s94
  store_step with Store.apply_rep s95 v96 v97 _ _ hinv95 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s96, hinv96, h_v98⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 h_v30 dropping h_v96 h_v97 hinv95 s95 v96 v97
  store_step with Store.apply_rep s96 v30 v98 _ _ hinv96 h64 h_v30 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s97, hinv97, h_v99⟩ growing hG carrying h_v2 h_v13 h_v23 h_v24 dropping h_v30 h_v98 hinv96 s96 v30 v98
  store_step with Store.apply_rep s97 v24 v99 _ _ hinv97 h64 h_v24 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s98, hinv98, h_v100⟩ growing hG carrying h_v2 h_v13 h_v23 dropping h_v24 h_v99 hinv97 s97 v24 v99
  store_step with Store.literal_boolean_spec s98 true hinv98 h64 as ⟨v101, s99, hinv99, h_v101⟩ growing hG carrying h_v2 h_v13 h_v23 h_v100 dropping hinv98 s98
  store_step with Store.apply_rep s99 v100 v101 _ _ hinv99 h64 h_v100 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s100, hinv100, h_v102⟩ growing hG carrying h_v2 h_v13 h_v23 dropping h_v100 h_v101 hinv99 s99 v100 v101
  store_step with Store.apply_rep s100 v23 v102 _ _ hinv100 h64 h_v23 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s101, hinv101, h_v103⟩ growing hG carrying h_v2 h_v13 dropping h_v102 h_v23 hinv100 s100 v102 v23
  store_step with Store.apply_rep s101 v13 v103 _ _ hinv101 h64 h_v13 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s102, hinv102, h_v104⟩ growing hG carrying h_v2 dropping h_v103 h_v13 hinv101 s101 v103 v13
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo_and.construct s102 e_v105 (by rw [he_v105]; exact empty_args) hinv102 h64 as ⟨v105, s103, hinv103, h_v105⟩ growing hG carrying h_v2 h_v104 dropping he_v105 hinv102 e_v105 s102
  step as ⟨e_v106, he_v106⟩
  store_step with CtorSpec.eo__3d.construct s103 e_v106 (by rw [he_v106]; exact empty_args) hinv103 h64 as ⟨v106, s104, hinv104, h_v106⟩ growing hG carrying h_v2 h_v104 h_v105 dropping he_v106 hinv103 e_v106 s103
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo__40purify.construct s104 e_v107 (by rw [he_v107]; exact empty_args) hinv104 h64 as ⟨v107, s105, hinv105, h_v107⟩ growing hG carrying h_v2 h_v104 h_v105 h_v106 dropping he_v107 hinv104 e_v107 s104
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s105 e_v108 (by rw [he_v108]; exact empty_args) hinv105 h64 as ⟨v108, s106, hinv106, h_v108⟩ growing hG carrying h_v2 h_v104 h_v105 h_v106 h_v107 dropping he_v108 hinv105 e_v108 s105
  store_step with Store.apply_rep s106 v108 v2 _ _ hinv106 h64 h_v108 h_v2 (by ns_tac) (by ns_tac) as ⟨v109, s107, hinv107, h_v109⟩ growing hG carrying h_v2 h_v104 h_v105 h_v106 h_v107 dropping h_v108 hinv106 s106 v108
  store_step with Store.apply_rep s107 v107 v109 _ _ hinv107 h64 h_v107 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s108, hinv108, h_v110⟩ growing hG carrying h_v2 h_v104 h_v105 h_v106 dropping h_v107 h_v109 hinv107 s107 v107 v109
  store_step with Store.apply_rep s108 v106 v110 _ _ hinv108 h64 h_v106 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s109, hinv109, h_v111⟩ growing hG carrying h_v2 h_v104 h_v105 dropping h_v106 h_v110 hinv108 s108 v106 v110
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s109 e_v112 (by rw [he_v112]; exact empty_args) hinv109 h64 as ⟨v112, s110, hinv110, h_v112⟩ growing hG carrying h_v2 h_v104 h_v105 h_v111 dropping he_v112 hinv109 e_v112 s109
  store_step with Store.apply_rep s110 v112 v2 _ _ hinv110 h64 h_v112 h_v2 (by ns_tac) (by ns_tac) as ⟨v113, s111, hinv111, h_v113⟩ growing hG carrying h_v2 h_v104 h_v105 h_v111 dropping h_v112 hinv110 s110 v112
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_str_2elen.construct s111 e_v114 (by rw [he_v114]; exact empty_args) hinv111 h64 as ⟨v114, s112, hinv112, h_v114⟩ growing hG carrying h_v2 h_v104 h_v105 h_v111 h_v113 dropping he_v114 hinv111 e_v114 s111
  store_step with Store.apply_rep s112 v114 v2 _ _ hinv112 h64 h_v114 h_v2 (by ns_tac) (by ns_tac) as ⟨v115, s113, hinv113, h_v115⟩ growing hG carrying h_v2 h_v104 h_v105 h_v111 h_v113 dropping h_v114 hinv112 s112 v114
  store_step with Store.apply_rep s113 v113 v115 _ _ hinv113 h64 h_v113 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s114, hinv114, h_v116⟩ growing hG carrying h_v2 h_v104 h_v105 h_v111 dropping h_v113 h_v115 hinv113 s113 v113 v115
  store_step with Store.apply_rep s114 v111 v116 _ _ hinv114 h64 h_v111 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s115, hinv115, h_v117⟩ growing hG carrying h_v2 h_v104 h_v105 dropping h_v111 h_v116 hinv114 s114 v111 v116
  store_step with Store.apply_rep s115 v105 v117 _ _ hinv115 h64 h_v105 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s116, hinv116, h_v118⟩ growing hG carrying h_v2 h_v104 dropping h_v105 h_v117 hinv115 s115 v105 v117
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_and.construct s116 e_v119 (by rw [he_v119]; exact empty_args) hinv116 h64 as ⟨v119, s117, hinv117, h_v119⟩ growing hG carrying h_v2 h_v104 h_v118 dropping he_v119 hinv116 e_v119 s116
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo__3d.construct s117 e_v120 (by rw [he_v120]; exact empty_args) hinv117 h64 as ⟨v120, s118, hinv118, h_v120⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 dropping he_v120 hinv117 e_v120 s117
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s118 0#u32 (0) (by scalar_tac) hinv118 h64 as ⟨v121, s119, hinv119, h_v121⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 h_v120 dropping hinv118 s118
  store_step with Store.apply_rep s119 v120 v121 _ _ hinv119 h64 h_v120 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s120, hinv120, h_v122⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 dropping h_v120 h_v121 hinv119 s119 v120 v121
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s120 e_v123 (by rw [he_v123]; exact empty_args) hinv120 h64 as ⟨v123, s121, hinv121, h_v123⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 h_v122 dropping he_v123 hinv120 e_v123 s120
  store_step with Store.apply_rep s121 v123 v2 _ _ hinv121 h64 h_v123 h_v2 (by ns_tac) (by ns_tac) as ⟨v124, s122, hinv122, h_v124⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 h_v122 dropping h_v123 hinv121 s121 v123
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s122 0#u32 (0) (by scalar_tac) hinv122 h64 as ⟨v125, s123, hinv123, h_v125⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 h_v122 h_v124 dropping hinv122 s122
  store_step with Store.apply_rep s123 v124 v125 _ _ hinv123 h64 h_v124 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s124, hinv124, h_v126⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 h_v122 dropping h_v124 h_v125 hinv123 s123 v124 v125
  store_step with Store.apply_rep s124 v122 v126 _ _ hinv124 h64 h_v122 h_v126 (by ns_tac) (by ns_tac) as ⟨v127, s125, hinv125, h_v127⟩ growing hG carrying h_v2 h_v104 h_v118 h_v119 dropping h_v122 h_v126 hinv124 s124 v122 v126
  store_step with Store.apply_rep s125 v119 v127 _ _ hinv125 h64 h_v119 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s126, hinv126, h_v128⟩ growing hG carrying h_v2 h_v104 h_v118 dropping h_v119 h_v127 hinv125 s125 v119 v127
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo_and.construct s126 e_v129 (by rw [he_v129]; exact empty_args) hinv126 h64 as ⟨v129, s127, hinv127, h_v129⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 dropping he_v129 hinv126 e_v129 s126
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo__3e.construct s127 e_v130 (by rw [he_v130]; exact empty_args) hinv127 h64 as ⟨v130, s128, hinv128, h_v130⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v129 dropping he_v130 hinv127 e_v130 s127
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_str_2elen.construct s128 e_v131 (by rw [he_v131]; exact empty_args) hinv128 h64 as ⟨v131, s129, hinv129, h_v131⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v129 h_v130 dropping he_v131 hinv128 e_v131 s128
  store_step with Store.apply_rep s129 v131 v2 _ _ hinv129 h64 h_v131 h_v2 (by ns_tac) (by ns_tac) as ⟨v132, s130, hinv130, h_v132⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v129 h_v130 dropping h_v131 hinv129 s129 v131
  store_step with Store.apply_rep s130 v130 v132 _ _ hinv130 h64 h_v130 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s131, hinv131, h_v133⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v129 dropping h_v130 h_v132 hinv130 s130 v130 v132
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s131 0#u32 (0) (by scalar_tac) hinv131 h64 as ⟨v134, s132, hinv132, h_v134⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v129 h_v133 dropping hinv131 s131
  store_step with Store.apply_rep s132 v133 v134 _ _ hinv132 h64 h_v133 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s133, hinv133, h_v135⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v129 dropping h_v133 h_v134 hinv132 s132 v133 v134
  store_step with Store.apply_rep s133 v129 v135 _ _ hinv133 h64 h_v129 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s134, hinv134, h_v136⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 dropping h_v129 h_v135 hinv133 s133 v129 v135
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo_and.construct s134 e_v137 (by rw [he_v137]; exact empty_args) hinv134 h64 as ⟨v137, s135, hinv135, h_v137⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 dropping he_v137 hinv134 e_v137 s134
  step as ⟨e_v138, he_v138⟩
  store_step with CtorSpec.eo_forall.construct s135 e_v138 (by rw [he_v138]; exact empty_args) hinv135 h64 as ⟨v138, s136, hinv136, h_v138⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 dropping he_v138 hinv135 e_v138 s135
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s136 e_v139 (by rw [he_v139]; exact empty_args) hinv136 h64 as ⟨v139, s137, hinv137, h_v139⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 dropping he_v139 hinv136 e_v139 s136
  step as ⟨e_v140, he_v140⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s137 _ _ rfl hinv137 h64 as ⟨v140, s138, hinv138, h_v140⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 h_v139 dropping hinv137 s137
  replace h_v140 := Represents.rep_of_eq h_v140 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v140]; decide)
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo_Int.construct s138 e_v141 (by rw [he_v141]; exact empty_args) hinv138 h64 as ⟨v141, s139, hinv139, h_v141⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 h_v139 h_v140 dropping he_v140 he_v141 hinv138 e_v140 e_v141 s138
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s139 e_v142 (by rw [he_v142]; rfl) h_v140 h_v141 hinv139 h64 as ⟨v142, s140, hinv140, h_v142⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 h_v139 dropping h_v140 h_v141 he_v142 hinv139 e_v142 s139 v140 v141
  store_step with Store.apply_rep s140 v139 v142 _ _ hinv140 h64 h_v139 h_v142 (by ns_tac) (by ns_tac) as ⟨v143, s141, hinv141, h_v143⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 dropping h_v139 h_v142 hinv140 s140 v139 v142
  step as ⟨e_v144, he_v144⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s141 e_v144 (by rw [he_v144]; exact empty_args) hinv141 h64 as ⟨v144, s142, hinv142, h_v144⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 h_v143 dropping he_v144 hinv141 e_v144 s141
  store_step with Store.apply_rep s142 v143 v144 _ _ hinv142 h64 h_v143 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s143, hinv143, h_v145⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v138 dropping h_v143 h_v144 hinv142 s142 v143 v144
  store_step with Store.apply_rep s143 v138 v145 _ _ hinv143 h64 h_v138 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s144, hinv144, h_v146⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 dropping h_v138 h_v145 hinv143 s143 v138 v145
  step as ⟨e_v147, he_v147⟩
  store_step with CtorSpec.eo_or.construct s144 e_v147 (by rw [he_v147]; exact empty_args) hinv144 h64 as ⟨v147, s145, hinv145, h_v147⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 dropping he_v147 hinv144 e_v147 s144
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo_not.construct s145 e_v148 (by rw [he_v148]; exact empty_args) hinv145 h64 as ⟨v148, s146, hinv146, h_v148⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 dropping he_v148 hinv145 e_v148 s145
  step as ⟨e_v149, he_v149⟩
  store_step with CtorSpec.eo__3e_3d.construct s146 e_v149 (by rw [he_v149]; exact empty_args) hinv146 h64 as ⟨v149, s147, hinv147, h_v149⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 dropping he_v149 hinv146 e_v149 s146
  step as ⟨e_v150, he_v150⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s147 _ _ rfl hinv147 h64 as ⟨v150, s148, hinv148, h_v150⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 h_v149 dropping hinv147 s147
  replace h_v150 := Represents.rep_of_eq h_v150 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v150]; decide)
  step as ⟨e_v151, he_v151⟩
  store_step with CtorSpec.eo_Int.construct s148 e_v151 (by rw [he_v151]; exact empty_args) hinv148 h64 as ⟨v151, s149, hinv149, h_v151⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 h_v149 h_v150 dropping he_v150 he_v151 hinv148 e_v150 e_v151 s148
  step as ⟨e_v152, he_v152⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s149 e_v152 (by rw [he_v152]; rfl) h_v150 h_v151 hinv149 h64 as ⟨v152, s150, hinv150, h_v152⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 h_v149 dropping h_v150 h_v151 he_v152 hinv149 e_v152 s149 v150 v151
  store_step with Store.apply_rep s150 v149 v152 _ _ hinv150 h64 h_v149 h_v152 (by ns_tac) (by ns_tac) as ⟨v153, s151, hinv151, h_v153⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 dropping h_v149 h_v152 hinv150 s150 v149 v152
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s151 0#u32 (0) (by scalar_tac) hinv151 h64 as ⟨v154, s152, hinv152, h_v154⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 h_v153 dropping hinv151 s151
  store_step with Store.apply_rep s152 v153 v154 _ _ hinv152 h64 h_v153 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s153, hinv153, h_v155⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 h_v148 dropping h_v153 h_v154 hinv152 s152 v153 v154
  store_step with Store.apply_rep s153 v148 v155 _ _ hinv153 h64 h_v148 h_v155 (by ns_tac) (by ns_tac) as ⟨v156, s154, hinv154, h_v156⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v147 dropping h_v148 h_v155 hinv153 s153 v148 v155
  store_step with Store.apply_rep s154 v147 v156 _ _ hinv154 h64 h_v147 h_v156 (by ns_tac) (by ns_tac) as ⟨v157, s155, hinv155, h_v157⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 dropping h_v147 h_v156 hinv154 s154 v147 v156
  step as ⟨e_v158, he_v158⟩
  store_step with CtorSpec.eo_or.construct s155 e_v158 (by rw [he_v158]; exact empty_args) hinv155 h64 as ⟨v158, s156, hinv156, h_v158⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 dropping he_v158 hinv155 e_v158 s155
  step as ⟨e_v159, he_v159⟩
  store_step with CtorSpec.eo_not.construct s156 e_v159 (by rw [he_v159]; exact empty_args) hinv156 h64 as ⟨v159, s157, hinv157, h_v159⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 dropping he_v159 hinv156 e_v159 s156
  step as ⟨e_v160, he_v160⟩
  store_step with CtorSpec.eo__3c.construct s157 e_v160 (by rw [he_v160]; exact empty_args) hinv157 h64 as ⟨v160, s158, hinv158, h_v160⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 dropping he_v160 hinv157 e_v160 s157
  step as ⟨e_v161, he_v161⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s158 _ _ rfl hinv158 h64 as ⟨v161, s159, hinv159, h_v161⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 h_v160 dropping hinv158 s158
  replace h_v161 := Represents.rep_of_eq h_v161 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v161]; decide)
  step as ⟨e_v162, he_v162⟩
  store_step with CtorSpec.eo_Int.construct s159 e_v162 (by rw [he_v162]; exact empty_args) hinv159 h64 as ⟨v162, s160, hinv160, h_v162⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 h_v160 h_v161 dropping he_v161 he_v162 hinv159 e_v161 e_v162 s159
  step as ⟨e_v163, he_v163⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s160 e_v163 (by rw [he_v163]; rfl) h_v161 h_v162 hinv160 h64 as ⟨v163, s161, hinv161, h_v163⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 h_v160 dropping h_v161 h_v162 he_v163 hinv160 e_v163 s160 v161 v162
  store_step with Store.apply_rep s161 v160 v163 _ _ hinv161 h64 h_v160 h_v163 (by ns_tac) (by ns_tac) as ⟨v164, s162, hinv162, h_v164⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 dropping h_v160 h_v163 hinv161 s161 v160 v163
  step as ⟨e_v165, he_v165⟩
  store_step with CtorSpec.eo_str_2elen.construct s162 e_v165 (by rw [he_v165]; exact empty_args) hinv162 h64 as ⟨v165, s163, hinv163, h_v165⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 h_v164 dropping he_v165 hinv162 e_v165 s162
  store_step with Store.apply_rep s163 v165 v2 _ _ hinv163 h64 h_v165 h_v2 (by ns_tac) (by ns_tac) as ⟨v166, s164, hinv164, h_v166⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 h_v164 dropping h_v165 hinv163 s163 v165
  store_step with Store.apply_rep s164 v164 v166 _ _ hinv164 h64 h_v164 h_v166 (by ns_tac) (by ns_tac) as ⟨v167, s165, hinv165, h_v167⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 h_v159 dropping h_v164 h_v166 hinv164 s164 v164 v166
  store_step with Store.apply_rep s165 v159 v167 _ _ hinv165 h64 h_v159 h_v167 (by ns_tac) (by ns_tac) as ⟨v168, s166, hinv166, h_v168⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v158 dropping h_v159 h_v167 hinv165 s165 v159 v167
  store_step with Store.apply_rep s166 v158 v168 _ _ hinv166 h64 h_v158 h_v168 (by ns_tac) (by ns_tac) as ⟨v169, s167, hinv167, h_v169⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 dropping h_v158 h_v168 hinv166 s166 v158 v168
  step as ⟨e_v170, he_v170⟩
  store_step with CtorSpec.eo_or.construct s167 e_v170 (by rw [he_v170]; exact empty_args) hinv167 h64 as ⟨v170, s168, hinv168, h_v170⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 dropping he_v170 hinv167 e_v170 s167
  step as ⟨e_v171, he_v171⟩
  store_step with CtorSpec.eo_and.construct s168 e_v171 (by rw [he_v171]; exact empty_args) hinv168 h64 as ⟨v171, s169, hinv169, h_v171⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 dropping he_v171 hinv168 e_v171 s168
  step as ⟨e_v172, he_v172⟩
  store_step with CtorSpec.eo__3d.construct s169 e_v172 (by rw [he_v172]; exact empty_args) hinv169 h64 as ⟨v172, s170, hinv170, h_v172⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 dropping he_v172 hinv169 e_v172 s169
  step as ⟨e_v173, he_v173⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s170 e_v173 (by rw [he_v173]; exact empty_args) hinv170 h64 as ⟨v173, s171, hinv171, h_v173⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 dropping he_v173 hinv170 e_v173 s170
  store_step with Store.apply_rep s171 v173 v2 _ _ hinv171 h64 h_v173 h_v2 (by ns_tac) (by ns_tac) as ⟨v174, s172, hinv172, h_v174⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 dropping h_v173 hinv171 s171 v173
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo__2b.construct s172 e_v175 (by rw [he_v175]; exact empty_args) hinv172 h64 as ⟨v175, s173, hinv173, h_v175⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 dropping he_v175 hinv172 e_v175 s172
  step as ⟨e_v176, he_v176⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s173 _ _ rfl hinv173 h64 as ⟨v176, s174, hinv174, h_v176⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v175 dropping hinv173 s173
  replace h_v176 := Represents.rep_of_eq h_v176 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v176]; decide)
  step as ⟨e_v177, he_v177⟩
  store_step with CtorSpec.eo_Int.construct s174 e_v177 (by rw [he_v177]; exact empty_args) hinv174 h64 as ⟨v177, s175, hinv175, h_v177⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v175 h_v176 dropping he_v176 he_v177 hinv174 e_v176 e_v177 s174
  step as ⟨e_v178, he_v178⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s175 e_v178 (by rw [he_v178]; rfl) h_v176 h_v177 hinv175 h64 as ⟨v178, s176, hinv176, h_v178⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v175 dropping h_v176 h_v177 he_v178 hinv175 e_v178 s175 v176 v177
  store_step with Store.apply_rep s176 v175 v178 _ _ hinv176 h64 h_v175 h_v178 (by ns_tac) (by ns_tac) as ⟨v179, s177, hinv177, h_v179⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 dropping h_v175 h_v178 hinv176 s176 v175 v178
  step as ⟨e_v180, he_v180⟩
  store_step with CtorSpec.eo__2b.construct s177 e_v180 (by rw [he_v180]; exact empty_args) hinv177 h64 as ⟨v180, s178, hinv178, h_v180⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v179 dropping he_v180 hinv177 e_v180 s177
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s178 1#u32 (1) (by scalar_tac) hinv178 h64 as ⟨v181, s179, hinv179, h_v181⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v179 h_v180 dropping hinv178 s178
  store_step with Store.apply_rep s179 v180 v181 _ _ hinv179 h64 h_v180 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s180, hinv180, h_v182⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v179 dropping h_v180 h_v181 hinv179 s179 v180 v181
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s180 0#u32 (0) (by scalar_tac) hinv180 h64 as ⟨v183, s181, hinv181, h_v183⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v179 h_v182 dropping hinv180 s180
  store_step with Store.apply_rep s181 v182 v183 _ _ hinv181 h64 h_v182 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s182, hinv182, h_v184⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 h_v179 dropping h_v182 h_v183 hinv181 s181 v182 v183
  store_step with Store.apply_rep s182 v179 v184 _ _ hinv182 h64 h_v179 h_v184 (by ns_tac) (by ns_tac) as ⟨v185, s183, hinv183, h_v185⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 h_v174 dropping h_v179 h_v184 hinv182 s182 v179 v184
  store_step with Store.apply_rep s183 v174 v185 _ _ hinv183 h64 h_v174 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s184, hinv184, h_v186⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v172 dropping h_v174 h_v185 hinv183 s183 v174 v185
  store_step with Store.apply_rep s184 v172 v186 _ _ hinv184 h64 h_v172 h_v186 (by ns_tac) (by ns_tac) as ⟨v187, s185, hinv185, h_v187⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 dropping h_v172 h_v186 hinv184 s184 v172 v186
  step as ⟨e_v188, he_v188⟩
  store_step with CtorSpec.eo__2b.construct s185 e_v188 (by rw [he_v188]; exact empty_args) hinv185 h64 as ⟨v188, s186, hinv186, h_v188⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 dropping he_v188 hinv185 e_v188 s185
  step as ⟨e_v189, he_v189⟩
  store_step with CtorSpec.eo__2d.construct s186 e_v189 (by rw [he_v189]; exact empty_args) hinv186 h64 as ⟨v189, s187, hinv187, h_v189⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 dropping he_v189 hinv186 e_v189 s186
  step as ⟨e_v190, he_v190⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s187 e_v190 (by rw [he_v190]; exact empty_args) hinv187 h64 as ⟨v190, s188, hinv188, h_v190⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 dropping he_v190 hinv187 e_v190 s187
  step as ⟨e_v191, he_v191⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s188 e_v191 (by rw [he_v191]; exact empty_args) hinv188 h64 as ⟨v191, s189, hinv189, h_v191⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 dropping he_v191 hinv188 e_v191 s188
  store_step with Store.apply_rep s189 v191 v2 _ _ hinv189 h64 h_v191 h_v2 (by ns_tac) (by ns_tac) as ⟨v192, s190, hinv190, h_v192⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 dropping h_v191 hinv189 s189 v191
  step as ⟨e_v193, he_v193⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s190 _ _ rfl hinv190 h64 as ⟨v193, s191, hinv191, h_v193⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 h_v192 dropping hinv190 s190
  replace h_v193 := Represents.rep_of_eq h_v193 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v193]; decide)
  step as ⟨e_v194, he_v194⟩
  store_step with CtorSpec.eo_Int.construct s191 e_v194 (by rw [he_v194]; exact empty_args) hinv191 h64 as ⟨v194, s192, hinv192, h_v194⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 h_v192 h_v193 dropping he_v193 he_v194 hinv191 e_v193 e_v194 s191
  step as ⟨e_v195, he_v195⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s192 e_v195 (by rw [he_v195]; rfl) h_v193 h_v194 hinv192 h64 as ⟨v195, s193, hinv193, h_v195⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 h_v192 dropping h_v193 h_v194 he_v195 hinv192 e_v195 s192 v193 v194
  store_step with Store.apply_rep s193 v192 v195 _ _ hinv193 h64 h_v192 h_v195 (by ns_tac) (by ns_tac) as ⟨v196, s194, hinv194, h_v196⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 dropping h_v192 h_v195 hinv193 s193 v192 v195
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s194 1#u32 (1) (by scalar_tac) hinv194 h64 as ⟨v197, s195, hinv195, h_v197⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 h_v196 dropping hinv194 s194
  store_step with Store.apply_rep s195 v196 v197 _ _ hinv195 h64 h_v196 h_v197 (by ns_tac) (by ns_tac) as ⟨v198, s196, hinv196, h_v198⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 h_v190 dropping h_v196 h_v197 hinv195 s195 v196 v197
  store_step with Store.apply_rep s196 v190 v198 _ _ hinv196 h64 h_v190 h_v198 (by ns_tac) (by ns_tac) as ⟨v199, s197, hinv197, h_v199⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v189 dropping h_v190 h_v198 hinv196 s196 v190 v198
  store_step with Store.apply_rep s197 v189 v199 _ _ hinv197 h64 h_v189 h_v199 (by ns_tac) (by ns_tac) as ⟨v200, s198, hinv198, h_v200⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 dropping h_v189 h_v199 hinv197 s197 v189 v199
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s198 48#u32 (48) (by scalar_tac) hinv198 h64 as ⟨v201, s199, hinv199, h_v201⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 h_v200 dropping hinv198 s198
  store_step with Store.apply_rep s199 v200 v201 _ _ hinv199 h64 h_v200 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s200, hinv200, h_v202⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v188 dropping h_v200 h_v201 hinv199 s199 v200 v201
  store_step with Store.apply_rep s200 v188 v202 _ _ hinv200 h64 h_v188 h_v202 (by ns_tac) (by ns_tac) as ⟨v203, s201, hinv201, h_v203⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 dropping h_v188 h_v202 hinv200 s200 v188 v202
  step as ⟨e_v204, he_v204⟩
  store_step with CtorSpec.eo__2b.construct s201 e_v204 (by rw [he_v204]; exact empty_args) hinv201 h64 as ⟨v204, s202, hinv202, h_v204⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 dropping he_v204 hinv201 e_v204 s201
  step as ⟨e_v205, he_v205⟩
  store_step with CtorSpec.eo__2a.construct s202 e_v205 (by rw [he_v205]; exact empty_args) hinv202 h64 as ⟨v205, s203, hinv203, h_v205⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 dropping he_v205 hinv202 e_v205 s202
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s203 10#u32 (10) (by scalar_tac) hinv203 h64 as ⟨v206, s204, hinv204, h_v206⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v205 dropping hinv203 s203
  store_step with Store.apply_rep s204 v205 v206 _ _ hinv204 h64 h_v205 h_v206 (by ns_tac) (by ns_tac) as ⟨v207, s205, hinv205, h_v207⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 dropping h_v205 h_v206 hinv204 s204 v205 v206
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo__2a.construct s205 e_v208 (by rw [he_v208]; exact empty_args) hinv205 h64 as ⟨v208, s206, hinv206, h_v208⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 dropping he_v208 hinv205 e_v208 s205
  step as ⟨e_v209, he_v209⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s206 e_v209 (by rw [he_v209]; exact empty_args) hinv206 h64 as ⟨v209, s207, hinv207, h_v209⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v208 dropping he_v209 hinv206 e_v209 s206
  store_step with Store.apply_rep s207 v209 v2 _ _ hinv207 h64 h_v209 h_v2 (by ns_tac) (by ns_tac) as ⟨v210, s208, hinv208, h_v210⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v208 dropping h_v209 hinv207 s207 v209
  step as ⟨e_v211, he_v211⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s208 _ _ rfl hinv208 h64 as ⟨v211, s209, hinv209, h_v211⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v208 h_v210 dropping hinv208 s208
  replace h_v211 := Represents.rep_of_eq h_v211 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v211]; decide)
  step as ⟨e_v212, he_v212⟩
  store_step with CtorSpec.eo_Int.construct s209 e_v212 (by rw [he_v212]; exact empty_args) hinv209 h64 as ⟨v212, s210, hinv210, h_v212⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v208 h_v210 h_v211 dropping he_v211 he_v212 hinv209 e_v211 e_v212 s209
  step as ⟨e_v213, he_v213⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s210 e_v213 (by rw [he_v213]; rfl) h_v211 h_v212 hinv210 h64 as ⟨v213, s211, hinv211, h_v213⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v208 h_v210 dropping h_v211 h_v212 he_v213 hinv210 e_v213 s210 v211 v212
  store_step with Store.apply_rep s211 v210 v213 _ _ hinv211 h64 h_v210 h_v213 (by ns_tac) (by ns_tac) as ⟨v214, s212, hinv212, h_v214⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v208 dropping h_v210 h_v213 hinv211 s211 v210 v213
  store_step with Store.apply_rep s212 v208 v214 _ _ hinv212 h64 h_v208 h_v214 (by ns_tac) (by ns_tac) as ⟨v215, s213, hinv213, h_v215⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 dropping h_v208 h_v214 hinv212 s212 v208 v214
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s213 1#u32 (1) (by scalar_tac) hinv213 h64 as ⟨v216, s214, hinv214, h_v216⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 h_v215 dropping hinv213 s213
  store_step with Store.apply_rep s214 v215 v216 _ _ hinv214 h64 h_v215 h_v216 (by ns_tac) (by ns_tac) as ⟨v217, s215, hinv215, h_v217⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 h_v207 dropping h_v215 h_v216 hinv214 s214 v215 v216
  store_step with Store.apply_rep s215 v207 v217 _ _ hinv215 h64 h_v207 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s216, hinv216, h_v218⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v204 dropping h_v207 h_v217 hinv215 s215 v207 v217
  store_step with Store.apply_rep s216 v204 v218 _ _ hinv216 h64 h_v204 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s217, hinv217, h_v219⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 dropping h_v204 h_v218 hinv216 s216 v204 v218
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s217 0#u32 (0) (by scalar_tac) hinv217 h64 as ⟨v220, s218, hinv218, h_v220⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 h_v219 dropping hinv217 s217
  store_step with Store.apply_rep s218 v219 v220 _ _ hinv218 h64 h_v219 h_v220 (by ns_tac) (by ns_tac) as ⟨v221, s219, hinv219, h_v221⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 h_v203 dropping h_v219 h_v220 hinv218 s218 v219 v220
  store_step with Store.apply_rep s219 v203 v221 _ _ hinv219 h64 h_v203 h_v221 (by ns_tac) (by ns_tac) as ⟨v222, s220, hinv220, h_v222⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 h_v187 dropping h_v203 h_v221 hinv219 s219 v203 v221
  store_step with Store.apply_rep s220 v187 v222 _ _ hinv220 h64 h_v187 h_v222 (by ns_tac) (by ns_tac) as ⟨v223, s221, hinv221, h_v223⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v171 dropping h_v187 h_v222 hinv220 s220 v187 v222
  store_step with Store.apply_rep s221 v171 v223 _ _ hinv221 h64 h_v171 h_v223 (by ns_tac) (by ns_tac) as ⟨v224, s222, hinv222, h_v224⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 dropping h_v171 h_v223 hinv221 s221 v171 v223
  step as ⟨e_v225, he_v225⟩
  store_step with CtorSpec.eo_and.construct s222 e_v225 (by rw [he_v225]; exact empty_args) hinv222 h64 as ⟨v225, s223, hinv223, h_v225⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 dropping he_v225 hinv222 e_v225 s222
  step as ⟨e_v226, he_v226⟩
  store_step with CtorSpec.eo_and.construct s223 e_v226 (by rw [he_v226]; exact empty_args) hinv223 h64 as ⟨v226, s224, hinv224, h_v226⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 dropping he_v226 hinv223 e_v226 s223
  step as ⟨e_v227, he_v227⟩
  store_step with CtorSpec.eo__3e_3d.construct s224 e_v227 (by rw [he_v227]; exact empty_args) hinv224 h64 as ⟨v227, s225, hinv225, h_v227⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 dropping he_v227 hinv224 e_v227 s224
  step as ⟨e_v228, he_v228⟩
  store_step with CtorSpec.eo__2d.construct s225 e_v228 (by rw [he_v228]; exact empty_args) hinv225 h64 as ⟨v228, s226, hinv226, h_v228⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 dropping he_v228 hinv225 e_v228 s225
  step as ⟨e_v229, he_v229⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s226 e_v229 (by rw [he_v229]; exact empty_args) hinv226 h64 as ⟨v229, s227, hinv227, h_v229⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 dropping he_v229 hinv226 e_v229 s226
  step as ⟨e_v230, he_v230⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s227 e_v230 (by rw [he_v230]; exact empty_args) hinv227 h64 as ⟨v230, s228, hinv228, h_v230⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 dropping he_v230 hinv227 e_v230 s227
  store_step with Store.apply_rep s228 v230 v2 _ _ hinv228 h64 h_v230 h_v2 (by ns_tac) (by ns_tac) as ⟨v231, s229, hinv229, h_v231⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 dropping h_v230 hinv228 s228 v230
  step as ⟨e_v232, he_v232⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s229 _ _ rfl hinv229 h64 as ⟨v232, s230, hinv230, h_v232⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 h_v231 dropping hinv229 s229
  replace h_v232 := Represents.rep_of_eq h_v232 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v232]; decide)
  step as ⟨e_v233, he_v233⟩
  store_step with CtorSpec.eo_Int.construct s230 e_v233 (by rw [he_v233]; exact empty_args) hinv230 h64 as ⟨v233, s231, hinv231, h_v233⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 h_v231 h_v232 dropping he_v232 he_v233 hinv230 e_v232 e_v233 s230
  step as ⟨e_v234, he_v234⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s231 e_v234 (by rw [he_v234]; rfl) h_v232 h_v233 hinv231 h64 as ⟨v234, s232, hinv232, h_v234⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 h_v231 dropping h_v232 h_v233 he_v234 hinv231 e_v234 s231 v232 v233
  store_step with Store.apply_rep s232 v231 v234 _ _ hinv232 h64 h_v231 h_v234 (by ns_tac) (by ns_tac) as ⟨v235, s233, hinv233, h_v235⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 dropping h_v231 h_v234 hinv232 s232 v231 v234
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s233 1#u32 (1) (by scalar_tac) hinv233 h64 as ⟨v236, s234, hinv234, h_v236⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 h_v235 dropping hinv233 s233
  store_step with Store.apply_rep s234 v235 v236 _ _ hinv234 h64 h_v235 h_v236 (by ns_tac) (by ns_tac) as ⟨v237, s235, hinv235, h_v237⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 h_v229 dropping h_v235 h_v236 hinv234 s234 v235 v236
  store_step with Store.apply_rep s235 v229 v237 _ _ hinv235 h64 h_v229 h_v237 (by ns_tac) (by ns_tac) as ⟨v238, s236, hinv236, h_v238⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v228 dropping h_v229 h_v237 hinv235 s235 v229 v237
  store_step with Store.apply_rep s236 v228 v238 _ _ hinv236 h64 h_v228 h_v238 (by ns_tac) (by ns_tac) as ⟨v239, s237, hinv237, h_v239⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 dropping h_v228 h_v238 hinv236 s236 v228 v238
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s237 48#u32 (48) (by scalar_tac) hinv237 h64 as ⟨v240, s238, hinv238, h_v240⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 h_v239 dropping hinv237 s237
  store_step with Store.apply_rep s238 v239 v240 _ _ hinv238 h64 h_v239 h_v240 (by ns_tac) (by ns_tac) as ⟨v241, s239, hinv239, h_v241⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v227 dropping h_v239 h_v240 hinv238 s238 v239 v240
  store_step with Store.apply_rep s239 v227 v241 _ _ hinv239 h64 h_v227 h_v241 (by ns_tac) (by ns_tac) as ⟨v242, s240, hinv240, h_v242⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 dropping h_v227 h_v241 hinv239 s239 v227 v241
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s240 0#u32 (0) (by scalar_tac) hinv240 h64 as ⟨v243, s241, hinv241, h_v243⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 h_v242 dropping hinv240 s240
  store_step with Store.apply_rep s241 v242 v243 _ _ hinv241 h64 h_v242 h_v243 (by ns_tac) (by ns_tac) as ⟨v244, s242, hinv242, h_v244⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v226 dropping h_v242 h_v243 hinv241 s241 v242 v243
  store_step with Store.apply_rep s242 v226 v244 _ _ hinv242 h64 h_v226 h_v244 (by ns_tac) (by ns_tac) as ⟨v245, s243, hinv243, h_v245⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 dropping h_v226 h_v244 hinv242 s242 v226 v244
  step as ⟨e_v246, he_v246⟩
  store_step with CtorSpec.eo_and.construct s243 e_v246 (by rw [he_v246]; exact empty_args) hinv243 h64 as ⟨v246, s244, hinv244, h_v246⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 dropping he_v246 hinv243 e_v246 s243
  step as ⟨e_v247, he_v247⟩
  store_step with CtorSpec.eo__3c.construct s244 e_v247 (by rw [he_v247]; exact empty_args) hinv244 h64 as ⟨v247, s245, hinv245, h_v247⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 dropping he_v247 hinv244 e_v247 s244
  step as ⟨e_v248, he_v248⟩
  store_step with CtorSpec.eo__2d.construct s245 e_v248 (by rw [he_v248]; exact empty_args) hinv245 h64 as ⟨v248, s246, hinv246, h_v248⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 dropping he_v248 hinv245 e_v248 s245
  step as ⟨e_v249, he_v249⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s246 e_v249 (by rw [he_v249]; exact empty_args) hinv246 h64 as ⟨v249, s247, hinv247, h_v249⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 dropping he_v249 hinv246 e_v249 s246
  step as ⟨e_v250, he_v250⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s247 e_v250 (by rw [he_v250]; exact empty_args) hinv247 h64 as ⟨v250, s248, hinv248, h_v250⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 dropping he_v250 hinv247 e_v250 s247
  store_step with Store.apply_rep s248 v250 v2 _ _ hinv248 h64 h_v250 h_v2 (by ns_tac) (by ns_tac) as ⟨v251, s249, hinv249, h_v251⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 dropping h_v250 hinv248 s248 v250
  step as ⟨e_v252, he_v252⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s249 _ _ rfl hinv249 h64 as ⟨v252, s250, hinv250, h_v252⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 h_v251 dropping hinv249 s249
  replace h_v252 := Represents.rep_of_eq h_v252 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v252]; decide)
  step as ⟨e_v253, he_v253⟩
  store_step with CtorSpec.eo_Int.construct s250 e_v253 (by rw [he_v253]; exact empty_args) hinv250 h64 as ⟨v253, s251, hinv251, h_v253⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 h_v251 h_v252 dropping he_v252 he_v253 hinv250 e_v252 e_v253 s250
  step as ⟨e_v254, he_v254⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s251 e_v254 (by rw [he_v254]; rfl) h_v252 h_v253 hinv251 h64 as ⟨v254, s252, hinv252, h_v254⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 h_v251 dropping h_v252 h_v253 he_v254 hinv251 e_v254 s251 v252 v253
  store_step with Store.apply_rep s252 v251 v254 _ _ hinv252 h64 h_v251 h_v254 (by ns_tac) (by ns_tac) as ⟨v255, s253, hinv253, h_v255⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 dropping h_v251 h_v254 hinv252 s252 v251 v254
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s253 1#u32 (1) (by scalar_tac) hinv253 h64 as ⟨v256, s254, hinv254, h_v256⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 h_v255 dropping hinv253 s253
  store_step with Store.apply_rep s254 v255 v256 _ _ hinv254 h64 h_v255 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s255, hinv255, h_v257⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 h_v249 dropping h_v255 h_v256 hinv254 s254 v255 v256
  store_step with Store.apply_rep s255 v249 v257 _ _ hinv255 h64 h_v249 h_v257 (by ns_tac) (by ns_tac) as ⟨v258, s256, hinv256, h_v258⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v248 dropping h_v249 h_v257 hinv255 s255 v249 v257
  store_step with Store.apply_rep s256 v248 v258 _ _ hinv256 h64 h_v248 h_v258 (by ns_tac) (by ns_tac) as ⟨v259, s257, hinv257, h_v259⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 dropping h_v248 h_v258 hinv256 s256 v248 v258
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s257 48#u32 (48) (by scalar_tac) hinv257 h64 as ⟨v260, s258, hinv258, h_v260⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 h_v259 dropping hinv257 s257
  store_step with Store.apply_rep s258 v259 v260 _ _ hinv258 h64 h_v259 h_v260 (by ns_tac) (by ns_tac) as ⟨v261, s259, hinv259, h_v261⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v247 dropping h_v259 h_v260 hinv258 s258 v259 v260
  store_step with Store.apply_rep s259 v247 v261 _ _ hinv259 h64 h_v247 h_v261 (by ns_tac) (by ns_tac) as ⟨v262, s260, hinv260, h_v262⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 dropping h_v247 h_v261 hinv259 s259 v247 v261
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s260 10#u32 (10) (by scalar_tac) hinv260 h64 as ⟨v263, s261, hinv261, h_v263⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 h_v262 dropping hinv260 s260
  store_step with Store.apply_rep s261 v262 v263 _ _ hinv261 h64 h_v262 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s262, hinv262, h_v264⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v246 dropping h_v262 h_v263 hinv261 s261 v262 v263
  store_step with Store.apply_rep s262 v246 v264 _ _ hinv262 h64 h_v246 h_v264 (by ns_tac) (by ns_tac) as ⟨v265, s263, hinv263, h_v265⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 dropping h_v246 h_v264 hinv262 s262 v246 v264
  store_step with Store.literal_boolean_spec s263 true hinv263 h64 as ⟨v266, s264, hinv264, h_v266⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 h_v265 dropping hinv263 s263
  store_step with Store.apply_rep s264 v265 v266 _ _ hinv264 h64 h_v265 h_v266 (by ns_tac) (by ns_tac) as ⟨v267, s265, hinv265, h_v267⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 h_v245 dropping h_v265 h_v266 hinv264 s264 v265 v266
  store_step with Store.apply_rep s265 v245 v267 _ _ hinv265 h64 h_v245 h_v267 (by ns_tac) (by ns_tac) as ⟨v268, s266, hinv266, h_v268⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v225 dropping h_v245 h_v267 hinv265 s265 v245 v267
  store_step with Store.apply_rep s266 v225 v268 _ _ hinv266 h64 h_v225 h_v268 (by ns_tac) (by ns_tac) as ⟨v269, s267, hinv267, h_v269⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 dropping h_v225 h_v268 hinv266 s266 v225 v268
  step as ⟨e_v270, he_v270⟩
  store_step with CtorSpec.eo_and.construct s267 e_v270 (by rw [he_v270]; exact empty_args) hinv267 h64 as ⟨v270, s268, hinv268, h_v270⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 dropping he_v270 hinv267 e_v270 s267
  step as ⟨e_v271, he_v271⟩
  store_step with CtorSpec.eo__3e_3d.construct s268 e_v271 (by rw [he_v271]; exact empty_args) hinv268 h64 as ⟨v271, s269, hinv269, h_v271⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 dropping he_v271 hinv268 e_v271 s268
  step as ⟨e_v272, he_v272⟩
  store_step with CtorSpec.eo__40purify.construct s269 e_v272 (by rw [he_v272]; exact empty_args) hinv269 h64 as ⟨v272, s270, hinv270, h_v272⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v271 dropping he_v272 hinv269 e_v272 s269
  step as ⟨e_v273, he_v273⟩
  store_step with CtorSpec.eo_str_2eto_5fint.construct s270 e_v273 (by rw [he_v273]; exact empty_args) hinv270 h64 as ⟨v273, s271, hinv271, h_v273⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v271 h_v272 dropping he_v273 hinv270 e_v273 s270
  store_step with Store.apply_rep s271 v273 v2 _ _ hinv271 h64 h_v273 h_v2 (by ns_tac) (by ns_tac) as ⟨v274, s272, hinv272, h_v274⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v271 h_v272 dropping h_v273 hinv271 s271 v273
  store_step with Store.apply_rep s272 v272 v274 _ _ hinv272 h64 h_v272 h_v274 (by ns_tac) (by ns_tac) as ⟨v275, s273, hinv273, h_v275⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v271 dropping h_v272 h_v274 hinv272 s272 v272 v274
  store_step with Store.apply_rep s273 v271 v275 _ _ hinv273 h64 h_v271 h_v275 (by ns_tac) (by ns_tac) as ⟨v276, s274, hinv274, h_v276⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 dropping h_v271 h_v275 hinv273 s273 v271 v275
  step as ⟨e_v277, he_v277⟩
  store_step with CtorSpec.eo__40strings_5fstoi_5fresult.construct s274 e_v277 (by rw [he_v277]; exact empty_args) hinv274 h64 as ⟨v277, s275, hinv275, h_v277⟩ growing hG carrying h_v2 h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 dropping he_v277 hinv274 e_v277 s274
  store_step with Store.apply_rep s275 v277 v2 _ _ hinv275 h64 h_v277 h_v2 (by ns_tac) (by ns_tac) as ⟨v278, s276, hinv276, h_v278⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 dropping h_v2 h_v277 hinv275 s275 v2 v277
  step as ⟨e_v279, he_v279⟩
  store_step with CtorSpec.eo__2b.construct s276 e_v279 (by rw [he_v279]; exact empty_args) hinv276 h64 as ⟨v279, s277, hinv277, h_v279⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 dropping he_v279 hinv276 e_v279 s276
  step as ⟨e_v280, he_v280⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s277 _ _ rfl hinv277 h64 as ⟨v280, s278, hinv278, h_v280⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v279 dropping hinv277 s277
  replace h_v280 := Represents.rep_of_eq h_v280 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v280]; decide)
  step as ⟨e_v281, he_v281⟩
  store_step with CtorSpec.eo_Int.construct s278 e_v281 (by rw [he_v281]; exact empty_args) hinv278 h64 as ⟨v281, s279, hinv279, h_v281⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v279 h_v280 dropping he_v280 he_v281 hinv278 e_v280 e_v281 s278
  step as ⟨e_v282, he_v282⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s279 e_v282 (by rw [he_v282]; rfl) h_v280 h_v281 hinv279 h64 as ⟨v282, s280, hinv280, h_v282⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v279 dropping h_v280 h_v281 he_v282 hinv279 e_v282 s279 v280 v281
  store_step with Store.apply_rep s280 v279 v282 _ _ hinv280 h64 h_v279 h_v282 (by ns_tac) (by ns_tac) as ⟨v283, s281, hinv281, h_v283⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 dropping h_v279 h_v282 hinv280 s280 v279 v282
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo__2b.construct s281 e_v284 (by rw [he_v284]; exact empty_args) hinv281 h64 as ⟨v284, s282, hinv282, h_v284⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v283 dropping he_v284 hinv281 e_v284 s281
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s282 1#u32 (1) (by scalar_tac) hinv282 h64 as ⟨v285, s283, hinv283, h_v285⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v283 h_v284 dropping hinv282 s282
  store_step with Store.apply_rep s283 v284 v285 _ _ hinv283 h64 h_v284 h_v285 (by ns_tac) (by ns_tac) as ⟨v286, s284, hinv284, h_v286⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v283 dropping h_v284 h_v285 hinv283 s283 v284 v285
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s284 0#u32 (0) (by scalar_tac) hinv284 h64 as ⟨v287, s285, hinv285, h_v287⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v283 h_v286 dropping hinv284 s284
  store_step with Store.apply_rep s285 v286 v287 _ _ hinv285 h64 h_v286 h_v287 (by ns_tac) (by ns_tac) as ⟨v288, s286, hinv286, h_v288⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 h_v283 dropping h_v286 h_v287 hinv285 s285 v286 v287
  store_step with Store.apply_rep s286 v283 v288 _ _ hinv286 h64 h_v283 h_v288 (by ns_tac) (by ns_tac) as ⟨v289, s287, hinv287, h_v289⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 h_v278 dropping h_v283 h_v288 hinv286 s286 v283 v288
  store_step with Store.apply_rep s287 v278 v289 _ _ hinv287 h64 h_v278 h_v289 (by ns_tac) (by ns_tac) as ⟨v290, s288, hinv288, h_v290⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 h_v276 dropping h_v278 h_v289 hinv287 s287 v278 v289
  store_step with Store.apply_rep s288 v276 v290 _ _ hinv288 h64 h_v276 h_v290 (by ns_tac) (by ns_tac) as ⟨v291, s289, hinv289, h_v291⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v270 dropping h_v276 h_v290 hinv288 s288 v276 v290
  store_step with Store.apply_rep s289 v270 v291 _ _ hinv289 h64 h_v270 h_v291 (by ns_tac) (by ns_tac) as ⟨v292, s290, hinv290, h_v292⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 dropping h_v270 h_v291 hinv289 s289 v270 v291
  store_step with Store.literal_boolean_spec s290 true hinv290 h64 as ⟨v293, s291, hinv291, h_v293⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 h_v292 dropping hinv290 s290
  store_step with Store.apply_rep s291 v292 v293 _ _ hinv291 h64 h_v292 h_v293 (by ns_tac) (by ns_tac) as ⟨v294, s292, hinv292, h_v294⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 h_v269 dropping h_v292 h_v293 hinv291 s291 v292 v293
  store_step with Store.apply_rep s292 v269 v294 _ _ hinv292 h64 h_v269 h_v294 (by ns_tac) (by ns_tac) as ⟨v295, s293, hinv293, h_v295⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 h_v224 dropping h_v269 h_v294 hinv292 s292 v269 v294
  store_step with Store.apply_rep s293 v224 v295 _ _ hinv293 h64 h_v224 h_v295 (by ns_tac) (by ns_tac) as ⟨v296, s294, hinv294, h_v296⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v170 dropping h_v224 h_v295 hinv293 s293 v224 v295
  store_step with Store.apply_rep s294 v170 v296 _ _ hinv294 h64 h_v170 h_v296 (by ns_tac) (by ns_tac) as ⟨v297, s295, hinv295, h_v297⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 dropping h_v170 h_v296 hinv294 s294 v170 v296
  store_step with Store.literal_boolean_spec s295 false hinv295 h64 as ⟨v298, s296, hinv296, h_v298⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 h_v297 dropping hinv295 s295
  store_step with Store.apply_rep s296 v297 v298 _ _ hinv296 h64 h_v297 h_v298 (by ns_tac) (by ns_tac) as ⟨v299, s297, hinv297, h_v299⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 h_v169 dropping h_v297 h_v298 hinv296 s296 v297 v298
  store_step with Store.apply_rep s297 v169 v299 _ _ hinv297 h64 h_v169 h_v299 (by ns_tac) (by ns_tac) as ⟨v300, s298, hinv298, h_v300⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 h_v157 dropping h_v169 h_v299 hinv297 s297 v169 v299
  store_step with Store.apply_rep s298 v157 v300 _ _ hinv298 h64 h_v157 h_v300 (by ns_tac) (by ns_tac) as ⟨v301, s299, hinv299, h_v301⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 h_v146 dropping h_v157 h_v300 hinv298 s298 v157 v300
  store_step with Store.apply_rep s299 v146 v301 _ _ hinv299 h64 h_v146 h_v301 (by ns_tac) (by ns_tac) as ⟨v302, s300, hinv300, h_v302⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v137 dropping h_v146 h_v301 hinv299 s299 v146 v301
  store_step with Store.apply_rep s300 v137 v302 _ _ hinv300 h64 h_v137 h_v302 (by ns_tac) (by ns_tac) as ⟨v303, s301, hinv301, h_v303⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 dropping h_v137 h_v302 hinv300 s300 v137 v302
  store_step with Store.literal_boolean_spec s301 true hinv301 h64 as ⟨v304, s302, hinv302, h_v304⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 h_v303 dropping hinv301 s301
  store_step with Store.apply_rep s302 v303 v304 _ _ hinv302 h64 h_v303 h_v304 (by ns_tac) (by ns_tac) as ⟨v305, s303, hinv303, h_v305⟩ growing hG carrying h_v104 h_v118 h_v128 h_v136 dropping h_v303 h_v304 hinv302 s302 v303 v304
  store_step with Store.apply_rep s303 v136 v305 _ _ hinv303 h64 h_v136 h_v305 (by ns_tac) (by ns_tac) as ⟨v306, s304, hinv304, h_v306⟩ growing hG carrying h_v104 h_v118 h_v128 dropping h_v136 h_v305 hinv303 s303 v136 v305
  store_step with Store.apply_rep s304 v128 v306 _ _ hinv304 h64 h_v128 h_v306 (by ns_tac) (by ns_tac) as ⟨v307, s305, hinv305, h_v307⟩ growing hG carrying h_v104 h_v118 dropping h_v128 h_v306 hinv304 s304 v128 v306
  store_step with Store.apply_rep s305 v118 v307 _ _ hinv305 h64 h_v118 h_v307 (by ns_tac) (by ns_tac) as ⟨v308, s306, hinv306, h_v308⟩ growing hG carrying h_v104 dropping h_v118 h_v307 hinv305 s305 v118 v307
  store_step with Store.apply_rep s306 v104 v308 _ _ hinv306 h64 h_v104 h_v308 (by ns_tac) (by ns_tac) as ⟨v309, s307, hinv307, h_v309⟩ growing hG carrying dropping h_v104 h_v308 hinv306 s306 v104 v308
  case_done hinv307 hG with h_v309 in EoCases.__str_reduction_pred.case_5 using hn_a0 hn_v1 hn_v2

set_option maxHeartbeats 4500000 in
theorem case_6_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_6_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_6
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_6
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_seq_2enth.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d_3e.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_and.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3e_3d.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 0#u32 (0) (by scalar_tac) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 h_v10 dropping hinv5 s5
  store_step with Store.apply_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 h_v11 hinv6 s6 v10 v11
  store_step with Store.apply_rep s7 v8 v12 _ _ hinv7 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v12 h_v8 hinv7 s7 v12 v8
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 dropping he_v14 hinv8 e_v14 s8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 h_v14 dropping he_v15 hinv9 e_v15 s9
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2elen.construct s10 e_v16 (by rw [he_v16]; exact empty_args) hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 h_v14 h_v15 dropping he_v16 hinv10 e_v16 s10
  store_step with Store.apply_rep s11 v16 v5 _ _ hinv11 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 h_v14 h_v15 dropping h_v16 hinv11 s11 v16
  store_step with Store.apply_rep s12 v15 v17 _ _ hinv12 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 h_v14 dropping h_v15 h_v17 hinv12 s12 v15 v17
  store_step with Store.apply_rep s13 v18 v2 _ _ hinv13 h64 h_v18 h_v2 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 h_v14 dropping h_v18 hinv13 s13 v18
  store_step with Store.apply_rep s14 v14 v19 _ _ hinv14 h64 h_v14 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 dropping h_v14 h_v19 hinv14 s14 v14 v19
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 h_v20 dropping hinv15 s15
  store_step with Store.apply_rep s16 v20 v21 _ _ hinv16 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v7 h_v13 dropping h_v20 h_v21 hinv16 s16 v20 v21
  store_step with Store.apply_rep s17 v13 v22 _ _ hinv17 h64 h_v13 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v13 h_v22 hinv17 s17 v13 v22
  store_step with Store.apply_rep s18 v7 v23 _ _ hinv18 h64 h_v7 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 dropping h_v23 h_v7 hinv18 s18 v23 v7
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_and.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v2 h_v5 h_v24 dropping he_v25 hinv19 e_v25 s19
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v26 (by rw [he_v26]; exact empty_args) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 dropping he_v26 hinv20 e_v26 s20
  store_step with Store.apply_rep s21 v26 v5 _ _ hinv21 h64 h_v26 h_v5 (by ns_tac) (by ns_tac) as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 dropping h_v26 hinv21 s21 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s22 e_v28 (by rw [he_v28]; exact empty_args) hinv22 h64 as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 dropping he_v28 hinv22 e_v28 s22
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__40purify.construct s23 e_v29 (by rw [he_v29]; exact empty_args) hinv23 h64 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 dropping he_v29 hinv23 e_v29 s23
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s24 e_v30 (by rw [he_v30]; exact empty_args) hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 h_v29 dropping he_v30 hinv24 e_v30 s24
  store_step with Store.apply_rep s25 v30 v5 _ _ hinv25 h64 h_v30 h_v5 (by ns_tac) (by ns_tac) as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 h_v29 dropping h_v30 hinv25 s25 v30
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s26 0#u32 (0) (by scalar_tac) hinv26 h64 as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 dropping hinv26 s26
  store_step with Store.apply_rep s27 v31 v32 _ _ hinv27 h64 h_v31 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 h_v29 dropping h_v31 h_v32 hinv27 s27 v31 v32
  store_step with Store.apply_rep s28 v33 v2 _ _ hinv28 h64 h_v33 h_v2 (by ns_tac) (by ns_tac) as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 h_v29 dropping h_v33 hinv28 s28 v33
  store_step with Store.apply_rep s29 v29 v34 _ _ hinv29 h64 h_v29 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v28 dropping h_v29 h_v34 hinv29 s29 v29 v34
  store_step with Store.apply_rep s30 v28 v35 _ _ hinv30 h64 h_v28 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 dropping h_v28 h_v35 hinv30 s30 v28 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s31 e_v37 (by rw [he_v37]; exact empty_args) hinv31 h64 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 dropping he_v37 hinv31 e_v37 s31
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s32 e_v38 (by rw [he_v38]; exact empty_args) hinv32 h64 as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 dropping he_v38 hinv32 e_v38 s32
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__40purify.construct s33 e_v39 (by rw [he_v39]; exact empty_args) hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 h_v38 dropping he_v39 hinv33 e_v39 s33
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_seq_2enth.construct s34 e_v40 (by rw [he_v40]; exact empty_args) hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 h_v38 h_v39 dropping he_v40 hinv34 e_v40 s34
  store_step with Store.apply_rep s35 v40 v5 _ _ hinv35 h64 h_v40 h_v5 (by ns_tac) (by ns_tac) as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 h_v38 h_v39 dropping h_v40 hinv35 s35 v40
  store_step with Store.apply_rep s36 v41 v2 _ _ hinv36 h64 h_v41 h_v2 (by ns_tac) (by ns_tac) as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 h_v38 h_v39 dropping h_v41 hinv36 s36 v41
  store_step with Store.apply_rep s37 v39 v42 _ _ hinv37 h64 h_v39 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 h_v38 dropping h_v39 h_v42 hinv37 s37 v39 v42
  store_step with Store.apply_rep s38 v38 v43 _ _ hinv38 h64 h_v38 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v37 dropping h_v38 h_v43 hinv38 s38 v38 v43
  store_step with Store.apply_rep s39 v37 v44 _ _ hinv39 h64 h_v37 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 dropping h_v37 h_v44 hinv39 s39 v37 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s40 e_v46 (by rw [he_v46]; exact empty_args) hinv40 h64 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 dropping he_v46 hinv40 e_v46 s40
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__40purify.construct s41 e_v47 (by rw [he_v47]; exact empty_args) hinv41 h64 as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 dropping he_v47 hinv41 e_v47 s41
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s42 e_v48 (by rw [he_v48]; exact empty_args) hinv42 h64 as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 dropping he_v48 hinv42 e_v48 s42
  store_step with Store.apply_rep s43 v48 v5 _ _ hinv43 h64 h_v48 h_v5 (by ns_tac) (by ns_tac) as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 dropping h_v48 hinv43 s43 v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo__2b.construct s44 e_v50 (by rw [he_v50]; exact empty_args) hinv44 h64 as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 dropping he_v50 hinv44 e_v50 s44
  store_step with Store.apply_rep s45 v50 v2 _ _ hinv45 h64 h_v50 h_v2 (by ns_tac) (by ns_tac) as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 dropping h_v50 hinv45 s45 v50
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__2b.construct s46 e_v52 (by rw [he_v52]; exact empty_args) hinv46 h64 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 h_v51 dropping he_v52 hinv46 e_v52 s46
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s47 1#u32 (1) (by scalar_tac) hinv47 h64 as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 h_v51 h_v52 dropping hinv47 s47
  store_step with Store.apply_rep s48 v52 v53 _ _ hinv48 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 h_v51 dropping h_v52 h_v53 hinv48 s48 v52 v53
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s49 0#u32 (0) (by scalar_tac) hinv49 h64 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 h_v51 h_v54 dropping hinv49 s49
  store_step with Store.apply_rep s50 v54 v55 _ _ hinv50 h64 h_v54 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 h_v51 dropping h_v54 h_v55 hinv50 s50 v54 v55
  store_step with Store.apply_rep s51 v51 v56 _ _ hinv51 h64 h_v51 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v49 dropping h_v51 h_v56 hinv51 s51 v51 v56
  store_step with Store.apply_rep s52 v49 v57 _ _ hinv52 h64 h_v49 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s53, hinv53, h_v58⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 dropping h_v49 h_v57 hinv52 s52 v49 v57
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__2d.construct s53 e_v59 (by rw [he_v59]; exact empty_args) hinv53 h64 as ⟨v59, s54, hinv54, h_v59⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 dropping he_v59 hinv53 e_v59 s53
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_str_2elen.construct s54 e_v60 (by rw [he_v60]; exact empty_args) hinv54 h64 as ⟨v60, s55, hinv55, h_v60⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v59 dropping he_v60 hinv54 e_v60 s54
  store_step with Store.apply_rep s55 v60 v5 _ _ hinv55 h64 h_v60 h_v5 (by ns_tac) (by ns_tac) as ⟨v61, s56, hinv56, h_v61⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v59 dropping h_v60 hinv55 s55 v60
  store_step with Store.apply_rep s56 v59 v61 _ _ hinv56 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s57, hinv57, h_v62⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 dropping h_v59 h_v61 hinv56 s56 v59 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo__2b.construct s57 e_v63 (by rw [he_v63]; exact empty_args) hinv57 h64 as ⟨v63, s58, hinv58, h_v63⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 dropping he_v63 hinv57 e_v63 s57
  store_step with Store.apply_rep s58 v63 v2 _ _ hinv58 h64 h_v63 h_v2 (by ns_tac) (by ns_tac) as ⟨v64, s59, hinv59, h_v64⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 dropping h_v63 hinv58 s58 v63
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__2b.construct s59 e_v65 (by rw [he_v65]; exact empty_args) hinv59 h64 as ⟨v65, s60, hinv60, h_v65⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 h_v64 dropping he_v65 hinv59 e_v65 s59
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s60 1#u32 (1) (by scalar_tac) hinv60 h64 as ⟨v66, s61, hinv61, h_v66⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 h_v64 h_v65 dropping hinv60 s60
  store_step with Store.apply_rep s61 v65 v66 _ _ hinv61 h64 h_v65 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s62, hinv62, h_v67⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 h_v64 dropping h_v65 h_v66 hinv61 s61 v65 v66
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s62 0#u32 (0) (by scalar_tac) hinv62 h64 as ⟨v68, s63, hinv63, h_v68⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 h_v64 h_v67 dropping hinv62 s62
  store_step with Store.apply_rep s63 v67 v68 _ _ hinv63 h64 h_v67 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s64, hinv64, h_v69⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 h_v64 dropping h_v67 h_v68 hinv63 s63 v67 v68
  store_step with Store.apply_rep s64 v64 v69 _ _ hinv64 h64 h_v64 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s65, hinv65, h_v70⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 h_v62 dropping h_v64 h_v69 hinv64 s64 v64 v69
  store_step with Store.apply_rep s65 v62 v70 _ _ hinv65 h64 h_v62 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s66, hinv66, h_v71⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 h_v58 dropping h_v62 h_v70 hinv65 s65 v62 v70
  store_step with Store.apply_rep s66 v58 v71 _ _ hinv66 h64 h_v58 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s67, hinv67, h_v72⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 h_v47 dropping h_v58 h_v71 hinv66 s66 v58 v71
  store_step with Store.apply_rep s67 v47 v72 _ _ hinv67 h64 h_v47 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s68, hinv68, h_v73⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v46 dropping h_v47 h_v72 hinv67 s67 v47 v72
  store_step with Store.apply_rep s68 v46 v73 _ _ hinv68 h64 h_v46 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s69, hinv69, h_v74⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 dropping h_v46 h_v73 hinv68 s68 v46 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s69 e_v75 (by rw [he_v75]; exact empty_args) hinv69 h64 as ⟨v75, s70, hinv70, h_v75⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 dropping he_v75 hinv69 e_v75 s69
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo__40purify.construct s70 e_v76 (by rw [he_v76]; exact empty_args) hinv70 h64 as ⟨v76, s71, hinv71, h_v76⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 dropping he_v76 hinv70 e_v76 s70
  step as ⟨e_v77, he_v77⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s71 e_v77 (by rw [he_v77]; exact empty_args) hinv71 h64 as ⟨v77, s72, hinv72, h_v77⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 h_v76 dropping he_v77 hinv71 e_v77 s71
  store_step with Store.apply_rep s72 v77 v5 _ _ hinv72 h64 h_v77 h_v5 (by ns_tac) (by ns_tac) as ⟨v78, s73, hinv73, h_v78⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 h_v76 dropping h_v77 hinv72 s72 v77
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s73 0#u32 (0) (by scalar_tac) hinv73 h64 as ⟨v79, s74, hinv74, h_v79⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 h_v76 h_v78 dropping hinv73 s73
  store_step with Store.apply_rep s74 v78 v79 _ _ hinv74 h64 h_v78 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s75, hinv75, h_v80⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 h_v76 dropping h_v78 h_v79 hinv74 s74 v78 v79
  store_step with Store.apply_rep s75 v80 v2 _ _ hinv75 h64 h_v80 h_v2 (by ns_tac) (by ns_tac) as ⟨v81, s76, hinv76, h_v81⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 h_v76 dropping h_v80 hinv75 s75 v80
  store_step with Store.apply_rep s76 v76 v81 _ _ hinv76 h64 h_v76 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s77, hinv77, h_v82⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 dropping h_v76 h_v81 hinv76 s76 v76 v81
  store_step with ih.eo__24eo_5ftypeof s77 v82 _ hinv77 h64 (hG.rem hrem) h_v82 as ⟨v83, s78, hinv78, h_v83⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 h_v75 dropping h_v82 hinv77 s77 v82
  store_step with ih.eo__24eo_5fnil s78 v75 v83 _ _ hinv78 h64 (hG.rem hrem) h_v75 h_v83 as ⟨v84, s79, hinv79, h_v84⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 h_v74 dropping h_v75 h_v83 hinv78 s78 v75 v83
  store_step with Store.apply_mk_rep s79 v74 v84 _ _ hinv79 h64 h_v74 h_v84 as ⟨v85, s80, hinv80, h_v85⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 h_v45 dropping h_v74 h_v84 hinv79 s79 v74 v84
  store_step with Store.apply_mk_rep s80 v45 v85 _ _ hinv80 h64 h_v45 h_v85 as ⟨v86, s81, hinv81, h_v86⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 h_v36 dropping h_v45 h_v85 hinv80 s80 v45 v85
  store_step with Store.apply_mk_rep s81 v36 v86 _ _ hinv81 h64 h_v36 h_v86 as ⟨v87, s82, hinv82, h_v87⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 h_v27 dropping h_v36 h_v86 hinv81 s81 v36 v86
  store_step with Store.apply_mk_rep s82 v27 v87 _ _ hinv82 h64 h_v27 h_v87 as ⟨v88, s83, hinv83, h_v88⟩ growing hG carrying h_v2 h_v5 h_v24 h_v25 dropping h_v27 h_v87 hinv82 s82 v27 v87
  store_step with Store.apply_mk_rep s83 v25 v88 _ _ hinv83 h64 h_v25 h_v88 as ⟨v89, s84, hinv84, h_v89⟩ growing hG carrying h_v2 h_v5 h_v24 dropping h_v25 h_v88 hinv83 s83 v25 v88
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_and.construct s84 e_v90 (by rw [he_v90]; exact empty_args) hinv84 h64 as ⟨v90, s85, hinv85, h_v90⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 dropping he_v90 hinv84 e_v90 s84
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__3d.construct s85 e_v91 (by rw [he_v91]; exact empty_args) hinv85 h64 as ⟨v91, s86, hinv86, h_v91⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 dropping he_v91 hinv85 e_v91 s85
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_str_2elen.construct s86 e_v92 (by rw [he_v92]; exact empty_args) hinv86 h64 as ⟨v92, s87, hinv87, h_v92⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 dropping he_v92 hinv86 e_v92 s86
  step as ⟨e_v93, he_v93⟩
  store_step with CtorSpec.eo__40purify.construct s87 e_v93 (by rw [he_v93]; exact empty_args) hinv87 h64 as ⟨v93, s88, hinv88, h_v93⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 dropping he_v93 hinv87 e_v93 s87
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s88 e_v94 (by rw [he_v94]; exact empty_args) hinv88 h64 as ⟨v94, s89, hinv89, h_v94⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 h_v93 dropping he_v94 hinv88 e_v94 s88
  store_step with Store.apply_rep s89 v94 v5 _ _ hinv89 h64 h_v94 h_v5 (by ns_tac) (by ns_tac) as ⟨v95, s90, hinv90, h_v95⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 h_v93 dropping h_v94 hinv89 s89 v94
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s90 0#u32 (0) (by scalar_tac) hinv90 h64 as ⟨v96, s91, hinv91, h_v96⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 h_v93 h_v95 dropping hinv90 s90
  store_step with Store.apply_rep s91 v95 v96 _ _ hinv91 h64 h_v95 h_v96 (by ns_tac) (by ns_tac) as ⟨v97, s92, hinv92, h_v97⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 h_v93 dropping h_v95 h_v96 hinv91 s91 v95 v96
  store_step with Store.apply_rep s92 v97 v2 _ _ hinv92 h64 h_v97 h_v2 (by ns_tac) (by ns_tac) as ⟨v98, s93, hinv93, h_v98⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 h_v93 dropping h_v97 hinv92 s92 v97
  store_step with Store.apply_rep s93 v93 v98 _ _ hinv93 h64 h_v93 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s94, hinv94, h_v99⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 h_v92 dropping h_v93 h_v98 hinv93 s93 v93 v98
  store_step with Store.apply_rep s94 v92 v99 _ _ hinv94 h64 h_v92 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s95, hinv95, h_v100⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 h_v91 dropping h_v92 h_v99 hinv94 s94 v92 v99
  store_step with Store.apply_rep s95 v91 v100 _ _ hinv95 h64 h_v91 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s96, hinv96, h_v101⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 dropping h_v100 h_v91 hinv95 s95 v100 v91
  store_step with Store.apply_rep s96 v101 v2 _ _ hinv96 h64 h_v101 h_v2 (by ns_tac) (by ns_tac) as ⟨v102, s97, hinv97, h_v102⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v90 dropping h_v101 hinv96 s96 v101
  store_step with Store.apply_rep s97 v90 v102 _ _ hinv97 h64 h_v90 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s98, hinv98, h_v103⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 dropping h_v102 h_v90 hinv97 s97 v102 v90
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_and.construct s98 e_v104 (by rw [he_v104]; exact empty_args) hinv98 h64 as ⟨v104, s99, hinv99, h_v104⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 dropping he_v104 hinv98 e_v104 s98
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__3d.construct s99 e_v105 (by rw [he_v105]; exact empty_args) hinv99 h64 as ⟨v105, s100, hinv100, h_v105⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 dropping he_v105 hinv99 e_v105 s99
  step as ⟨e_v106, he_v106⟩
  store_step with CtorSpec.eo_str_2elen.construct s100 e_v106 (by rw [he_v106]; exact empty_args) hinv100 h64 as ⟨v106, s101, hinv101, h_v106⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 dropping he_v106 hinv100 e_v106 s100
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo__40purify.construct s101 e_v107 (by rw [he_v107]; exact empty_args) hinv101 h64 as ⟨v107, s102, hinv102, h_v107⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 dropping he_v107 hinv101 e_v107 s101
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s102 e_v108 (by rw [he_v108]; exact empty_args) hinv102 h64 as ⟨v108, s103, hinv103, h_v108⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 dropping he_v108 hinv102 e_v108 s102
  store_step with Store.apply_rep s103 v108 v5 _ _ hinv103 h64 h_v108 h_v5 (by ns_tac) (by ns_tac) as ⟨v109, s104, hinv104, h_v109⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 dropping h_v108 hinv103 s103 v108
  step as ⟨e_v110, he_v110⟩
  store_step with CtorSpec.eo__2b.construct s104 e_v110 (by rw [he_v110]; exact empty_args) hinv104 h64 as ⟨v110, s105, hinv105, h_v110⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 dropping he_v110 hinv104 e_v110 s104
  store_step with Store.apply_rep s105 v110 v2 _ _ hinv105 h64 h_v110 h_v2 (by ns_tac) (by ns_tac) as ⟨v111, s106, hinv106, h_v111⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 dropping h_v110 hinv105 s105 v110
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo__2b.construct s106 e_v112 (by rw [he_v112]; exact empty_args) hinv106 h64 as ⟨v112, s107, hinv107, h_v112⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 h_v111 dropping he_v112 hinv106 e_v112 s106
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s107 1#u32 (1) (by scalar_tac) hinv107 h64 as ⟨v113, s108, hinv108, h_v113⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 h_v111 h_v112 dropping hinv107 s107
  store_step with Store.apply_rep s108 v112 v113 _ _ hinv108 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s109, hinv109, h_v114⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 h_v111 dropping h_v112 h_v113 hinv108 s108 v112 v113
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s109 0#u32 (0) (by scalar_tac) hinv109 h64 as ⟨v115, s110, hinv110, h_v115⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 h_v111 h_v114 dropping hinv109 s109
  store_step with Store.apply_rep s110 v114 v115 _ _ hinv110 h64 h_v114 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s111, hinv111, h_v116⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 h_v111 dropping h_v114 h_v115 hinv110 s110 v114 v115
  store_step with Store.apply_rep s111 v111 v116 _ _ hinv111 h64 h_v111 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s112, hinv112, h_v117⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v109 dropping h_v111 h_v116 hinv111 s111 v111 v116
  store_step with Store.apply_rep s112 v109 v117 _ _ hinv112 h64 h_v109 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s113, hinv113, h_v118⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 dropping h_v109 h_v117 hinv112 s112 v109 v117
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo__2d.construct s113 e_v119 (by rw [he_v119]; exact empty_args) hinv113 h64 as ⟨v119, s114, hinv114, h_v119⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 dropping he_v119 hinv113 e_v119 s113
  step as ⟨e_v120, he_v120⟩
  store_step with CtorSpec.eo_str_2elen.construct s114 e_v120 (by rw [he_v120]; exact empty_args) hinv114 h64 as ⟨v120, s115, hinv115, h_v120⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v119 dropping he_v120 hinv114 e_v120 s114
  store_step with Store.apply_rep s115 v120 v5 _ _ hinv115 h64 h_v120 h_v5 (by ns_tac) (by ns_tac) as ⟨v121, s116, hinv116, h_v121⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v119 dropping h_v120 hinv115 s115 v120
  store_step with Store.apply_rep s116 v119 v121 _ _ hinv116 h64 h_v119 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s117, hinv117, h_v122⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 dropping h_v119 h_v121 hinv116 s116 v119 v121
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo__2b.construct s117 e_v123 (by rw [he_v123]; exact empty_args) hinv117 h64 as ⟨v123, s118, hinv118, h_v123⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 dropping he_v123 hinv117 e_v123 s117
  store_step with Store.apply_rep s118 v123 v2 _ _ hinv118 h64 h_v123 h_v2 (by ns_tac) (by ns_tac) as ⟨v124, s119, hinv119, h_v124⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 dropping h_v123 hinv118 s118 v123
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo__2b.construct s119 e_v125 (by rw [he_v125]; exact empty_args) hinv119 h64 as ⟨v125, s120, hinv120, h_v125⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 h_v124 dropping he_v125 hinv119 e_v125 s119
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s120 1#u32 (1) (by scalar_tac) hinv120 h64 as ⟨v126, s121, hinv121, h_v126⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 h_v124 h_v125 dropping hinv120 s120
  store_step with Store.apply_rep s121 v125 v126 _ _ hinv121 h64 h_v125 h_v126 (by ns_tac) (by ns_tac) as ⟨v127, s122, hinv122, h_v127⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 h_v124 dropping h_v125 h_v126 hinv121 s121 v125 v126
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s122 0#u32 (0) (by scalar_tac) hinv122 h64 as ⟨v128, s123, hinv123, h_v128⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 h_v124 h_v127 dropping hinv122 s122
  store_step with Store.apply_rep s123 v127 v128 _ _ hinv123 h64 h_v127 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s124, hinv124, h_v129⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 h_v124 dropping h_v127 h_v128 hinv123 s123 v127 v128
  store_step with Store.apply_rep s124 v124 v129 _ _ hinv124 h64 h_v124 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s125, hinv125, h_v130⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 h_v122 dropping h_v124 h_v129 hinv124 s124 v124 v129
  store_step with Store.apply_rep s125 v122 v130 _ _ hinv125 h64 h_v122 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s126, hinv126, h_v131⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 h_v118 dropping h_v122 h_v130 hinv125 s125 v122 v130
  store_step with Store.apply_rep s126 v118 v131 _ _ hinv126 h64 h_v118 h_v131 (by ns_tac) (by ns_tac) as ⟨v132, s127, hinv127, h_v132⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 h_v107 dropping h_v118 h_v131 hinv126 s126 v118 v131
  store_step with Store.apply_rep s127 v107 v132 _ _ hinv127 h64 h_v107 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s128, hinv128, h_v133⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 h_v106 dropping h_v107 h_v132 hinv127 s127 v107 v132
  store_step with Store.apply_rep s128 v106 v133 _ _ hinv128 h64 h_v106 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s129, hinv129, h_v134⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v105 dropping h_v106 h_v133 hinv128 s128 v106 v133
  store_step with Store.apply_rep s129 v105 v134 _ _ hinv129 h64 h_v105 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s130, hinv130, h_v135⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 dropping h_v105 h_v134 hinv129 s129 v105 v134
  step as ⟨e_v136, he_v136⟩
  store_step with CtorSpec.eo__2d.construct s130 e_v136 (by rw [he_v136]; exact empty_args) hinv130 h64 as ⟨v136, s131, hinv131, h_v136⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v135 dropping he_v136 hinv130 e_v136 s130
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo_str_2elen.construct s131 e_v137 (by rw [he_v137]; exact empty_args) hinv131 h64 as ⟨v137, s132, hinv132, h_v137⟩ growing hG carrying h_v2 h_v5 h_v24 h_v89 h_v103 h_v104 h_v135 h_v136 dropping he_v137 hinv131 e_v137 s131
  store_step with Store.apply_rep s132 v137 v5 _ _ hinv132 h64 h_v137 h_v5 (by ns_tac) (by ns_tac) as ⟨v138, s133, hinv133, h_v138⟩ growing hG carrying h_v2 h_v24 h_v89 h_v103 h_v104 h_v135 h_v136 dropping h_v137 h_v5 hinv132 s132 v137 v5
  store_step with Store.apply_rep s133 v136 v138 _ _ hinv133 h64 h_v136 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s134, hinv134, h_v139⟩ growing hG carrying h_v2 h_v24 h_v89 h_v103 h_v104 h_v135 dropping h_v136 h_v138 hinv133 s133 v136 v138
  step as ⟨e_v140, he_v140⟩
  store_step with CtorSpec.eo__2b.construct s134 e_v140 (by rw [he_v140]; exact empty_args) hinv134 h64 as ⟨v140, s135, hinv135, h_v140⟩ growing hG carrying h_v2 h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 dropping he_v140 hinv134 e_v140 s134
  store_step with Store.apply_rep s135 v140 v2 _ _ hinv135 h64 h_v140 h_v2 (by ns_tac) (by ns_tac) as ⟨v141, s136, hinv136, h_v141⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 dropping h_v140 h_v2 hinv135 s135 v140 v2
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo__2b.construct s136 e_v142 (by rw [he_v142]; exact empty_args) hinv136 h64 as ⟨v142, s137, hinv137, h_v142⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 h_v141 dropping he_v142 hinv136 e_v142 s136
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s137 1#u32 (1) (by scalar_tac) hinv137 h64 as ⟨v143, s138, hinv138, h_v143⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 h_v141 h_v142 dropping hinv137 s137
  store_step with Store.apply_rep s138 v142 v143 _ _ hinv138 h64 h_v142 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s139, hinv139, h_v144⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 h_v141 dropping h_v142 h_v143 hinv138 s138 v142 v143
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s139 0#u32 (0) (by scalar_tac) hinv139 h64 as ⟨v145, s140, hinv140, h_v145⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 h_v141 h_v144 dropping hinv139 s139
  store_step with Store.apply_rep s140 v144 v145 _ _ hinv140 h64 h_v144 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s141, hinv141, h_v146⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 h_v141 dropping h_v144 h_v145 hinv140 s140 v144 v145
  store_step with Store.apply_rep s141 v141 v146 _ _ hinv141 h64 h_v141 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s142, hinv142, h_v147⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 h_v139 dropping h_v141 h_v146 hinv141 s141 v141 v146
  store_step with Store.apply_rep s142 v139 v147 _ _ hinv142 h64 h_v139 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s143, hinv143, h_v148⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 h_v135 dropping h_v139 h_v147 hinv142 s142 v139 v147
  store_step with Store.apply_rep s143 v135 v148 _ _ hinv143 h64 h_v135 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s144, hinv144, h_v149⟩ growing hG carrying h_v24 h_v89 h_v103 h_v104 dropping h_v135 h_v148 hinv143 s143 v135 v148
  store_step with Store.apply_rep s144 v104 v149 _ _ hinv144 h64 h_v104 h_v149 (by ns_tac) (by ns_tac) as ⟨v150, s145, hinv145, h_v150⟩ growing hG carrying h_v24 h_v89 h_v103 dropping h_v104 h_v149 hinv144 s144 v104 v149
  store_step with Store.literal_boolean_spec s145 true hinv145 h64 as ⟨v151, s146, hinv146, h_v151⟩ growing hG carrying h_v24 h_v89 h_v103 h_v150 dropping hinv145 s145
  store_step with Store.apply_rep s146 v150 v151 _ _ hinv146 h64 h_v150 h_v151 (by ns_tac) (by ns_tac) as ⟨v152, s147, hinv147, h_v152⟩ growing hG carrying h_v24 h_v89 h_v103 dropping h_v150 h_v151 hinv146 s146 v150 v151
  store_step with Store.apply_rep s147 v103 v152 _ _ hinv147 h64 h_v103 h_v152 (by ns_tac) (by ns_tac) as ⟨v153, s148, hinv148, h_v153⟩ growing hG carrying h_v24 h_v89 dropping h_v103 h_v152 hinv147 s147 v103 v152
  store_step with Store.apply_mk_rep s148 v89 v153 _ _ hinv148 h64 h_v89 h_v153 as ⟨v154, s149, hinv149, h_v154⟩ growing hG carrying h_v24 dropping h_v153 h_v89 hinv148 s148 v153 v89
  store_step with Store.apply_mk_rep s149 v24 v154 _ _ hinv149 h64 h_v24 h_v154 as ⟨v155, s150, hinv150, h_v155⟩ growing hG carrying dropping h_v154 h_v24 hinv149 s149 v154 v24
  case_done hinv150 hG with h_v155 in EoCases.__str_reduction_pred.case_6 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 9360000 in
theorem case_7_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_7_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_7
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_7
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_7
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
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 h_v23 dropping hinv15 s15
  store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v16 dropping h_v23 h_v24 hinv16 s16 v23 v24
  store_step with Store.apply_rep s17 v16 v25 _ _ hinv17 h64 h_v16 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v16 h_v25 hinv17 s17 v16 v25
  store_step with Store.apply_rep s18 v10 v26 _ _ hinv18 h64 h_v10 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v26 hinv18 s18 v10 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_and.construct s19 e_v28 (by rw [he_v28]; exact empty_args) hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 dropping he_v28 hinv19 e_v28 s19
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v29 (by rw [he_v29]; exact empty_args) hinv20 h64 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 dropping he_v29 hinv20 e_v29 s20
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__40purify.construct s21 e_v30 (by rw [he_v30]; exact empty_args) hinv21 h64 as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 dropping he_v30 hinv21 e_v30 s21
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s22 e_v31 (by rw [he_v31]; exact empty_args) hinv22 h64 as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 h_v30 dropping he_v31 hinv22 e_v31 s22
  store_step with Store.apply_rep s23 v31 v8 _ _ hinv23 h64 h_v31 h_v8 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 h_v30 dropping h_v31 hinv23 s23 v31
  store_step with Store.apply_rep s24 v32 v5 _ _ hinv24 h64 h_v32 h_v5 (by ns_tac) (by ns_tac) as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 h_v30 dropping h_v32 hinv24 s24 v32
  store_step with Store.apply_rep s25 v33 v2 _ _ hinv25 h64 h_v33 h_v2 (by ns_tac) (by ns_tac) as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 h_v30 dropping h_v33 hinv25 s25 v33
  store_step with Store.apply_rep s26 v30 v34 _ _ hinv26 h64 h_v30 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v29 dropping h_v30 h_v34 hinv26 s26 v30 v34
  store_step with Store.apply_rep s27 v29 v35 _ _ hinv27 h64 h_v29 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 dropping h_v29 h_v35 hinv27 s27 v29 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v37 (by rw [he_v37]; exact empty_args) hinv28 h64 as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 dropping he_v37 hinv28 e_v37 s28
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__40purify.construct s29 e_v38 (by rw [he_v38]; exact empty_args) hinv29 h64 as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 dropping he_v38 hinv29 e_v38 s29
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s30 e_v39 (by rw [he_v39]; exact empty_args) hinv30 h64 as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 h_v38 dropping he_v39 hinv30 e_v39 s30
  store_step with Store.apply_rep s31 v39 v8 _ _ hinv31 h64 h_v39 h_v8 (by ns_tac) (by ns_tac) as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 h_v38 dropping h_v39 hinv31 s31 v39
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 h_v38 h_v40 dropping hinv32 s32
  store_step with Store.apply_rep s33 v40 v41 _ _ hinv33 h64 h_v40 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 h_v38 dropping h_v40 h_v41 hinv33 s33 v40 v41
  store_step with Store.apply_rep s34 v42 v5 _ _ hinv34 h64 h_v42 h_v5 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 h_v38 dropping h_v42 hinv34 s34 v42
  store_step with Store.apply_rep s35 v38 v43 _ _ hinv35 h64 h_v38 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v37 dropping h_v38 h_v43 hinv35 s35 v38 v43
  store_step with Store.apply_rep s36 v37 v44 _ _ hinv36 h64 h_v37 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 dropping h_v37 h_v44 hinv36 s36 v37 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s37 e_v46 (by rw [he_v46]; exact empty_args) hinv37 h64 as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 dropping he_v46 hinv37 e_v46 s37
  store_step with ih.eo__24str_5fvalue_5flen s38 v2 _ hinv38 h64 (hG.rem hrem) h_v2 as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping hinv38 s38
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s39 1#u32 (1) (by scalar_tac) hinv39 h64 as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v47 dropping hinv39 s39
  step as ⟨e_v49, he_v49⟩
  store_step with Store.builtin_spec_is_eq s40 e_v49 (by rw [he_v49]; rfl) h_v47 h_v48 hinv40 h64 as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping h_v47 h_v48 he_v49 hinv40 e_v49 s40 v47 v48
  have h_ite_v60 := (show if_140_eo__24str_5freduction_5fpred s41 v49 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s41.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_140_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s41
    rcases Store.boolean_value_term h_v49 with ⟨hx_50, hbv_50⟩ | ⟨hx_50, hbv_50⟩ | ⟨hx_50, hbv_50⟩
    · ite_branch hbv_50
      ite_done hinv41 hG with (eo_ite_true_rep _ hx_50 h_v2)
    · ite_branch hbv_50
      step as ⟨e_v50, he_v50⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s41 e_v50 (by rw [he_v50]; exact empty_args) hinv41 h64 as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping h_v49 he_v50 e_v50 v49
      store_step with Store.apply_rep s42 v50 v2 _ _ hinv42 h64 h_v50 h_v2 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping h_v50 v50
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s43 0#u32 (0) (by scalar_tac) hinv43 h64 as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v51 dropping
      store_step with Store.apply_rep s44 v51 v52 _ _ hinv44 h64 h_v51 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping h_v51 h_v52 v51 v52
      step as ⟨e_v54, he_v54⟩
      store_step with CtorSpec.eo__2d.construct s45 e_v54 (by rw [he_v54]; exact empty_args) hinv45 h64 as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v53 dropping he_v54 e_v54
      step as ⟨e_v55, he_v55⟩
      store_step with CtorSpec.eo_str_2elen.construct s46 e_v55 (by rw [he_v55]; exact empty_args) hinv46 h64 as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v53 h_v54 dropping he_v55 e_v55
      store_step with Store.apply_rep s47 v55 v8 _ _ hinv47 h64 h_v55 h_v8 (by ns_tac) (by ns_tac) as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v53 h_v54 dropping h_v55 v55
      store_step with Store.apply_rep s48 v54 v56 _ _ hinv48 h64 h_v54 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v53 dropping h_v54 h_v56 v54 v56
      store_step with Store.apply_rep s49 v57 v5 _ _ hinv49 h64 h_v57 h_v5 (by ns_tac) (by ns_tac) as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 h_v53 dropping h_v57 v57
      store_step with Store.apply_rep s50 v53 v58 _ _ hinv50 h64 h_v53 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping h_v53 h_v58 v53 v58
      ite_done hinv51 hG with (eo_ite_false_rep _ hx_50 h_v59)
    · ite_branch hbv_50
      ite_stuck hinv41 hG with hx_50)
  store_step with h_ite_v60 as ⟨v60, s42, hinv42, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v46 dropping h_ite_v60 h_v49 hinv41 s41 v49
  store_step with Store.apply_mk_rep s42 v46 v60 _ _ hinv42 h64 h_v46 h_v60 as ⟨v61, s43, hinv43, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 dropping h_v46 h_v60 hinv42 s42 v46 v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s43 e_v62 (by rw [he_v62]; exact empty_args) hinv43 h64 as ⟨v62, s44, hinv44, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 dropping he_v62 hinv43 e_v62 s43
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo__40purify.construct s44 e_v63 (by rw [he_v63]; exact empty_args) hinv44 h64 as ⟨v63, s45, hinv45, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 dropping he_v63 hinv44 e_v63 s44
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s45 e_v64 (by rw [he_v64]; exact empty_args) hinv45 h64 as ⟨v64, s46, hinv46, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 dropping he_v64 hinv45 e_v64 s45
  store_step with Store.apply_rep s46 v64 v8 _ _ hinv46 h64 h_v64 h_v8 (by ns_tac) (by ns_tac) as ⟨v65, s47, hinv47, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 dropping h_v64 hinv46 s46 v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo__2b.construct s47 e_v66 (by rw [he_v66]; exact empty_args) hinv47 h64 as ⟨v66, s48, hinv48, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 dropping he_v66 hinv47 e_v66 s47
  store_step with Store.apply_rep s48 v66 v5 _ _ hinv48 h64 h_v66 h_v5 (by ns_tac) (by ns_tac) as ⟨v67, s49, hinv49, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 dropping h_v66 hinv48 s48 v66
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__2b.construct s49 e_v68 (by rw [he_v68]; exact empty_args) hinv49 h64 as ⟨v68, s50, hinv50, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 dropping he_v68 hinv49 e_v68 s49
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_str_2elen.construct s50 e_v69 (by rw [he_v69]; exact empty_args) hinv50 h64 as ⟨v69, s51, hinv51, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 dropping he_v69 hinv50 e_v69 s50
  store_step with ih.eo__24str_5fvalue_5flen s51 v2 _ hinv51 h64 (hG.rem hrem) h_v2 as ⟨v70, s52, hinv52, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping hinv51 s51
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s52 1#u32 (1) (by scalar_tac) hinv52 h64 as ⟨v71, s53, hinv53, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v70 dropping hinv52 s52
  step as ⟨e_v72, he_v72⟩
  store_step with Store.builtin_spec_is_eq s53 e_v72 (by rw [he_v72]; rfl) h_v70 h_v71 hinv53 h64 as ⟨v72, s54, hinv54, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping h_v70 h_v71 he_v72 hinv53 e_v72 s53 v70 v71
  have h_ite_v83 := (show if_141_eo__24str_5freduction_5fpred s54 v72 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s54.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_141_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s54
    rcases Store.boolean_value_term h_v72 with ⟨hx_73, hbv_73⟩ | ⟨hx_73, hbv_73⟩ | ⟨hx_73, hbv_73⟩
    · ite_branch hbv_73
      ite_done hinv54 hG with (eo_ite_true_rep _ hx_73 h_v2)
    · ite_branch hbv_73
      step as ⟨e_v73, he_v73⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s54 e_v73 (by rw [he_v73]; exact empty_args) hinv54 h64 as ⟨v73, s55, hinv55, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping h_v72 he_v73 e_v73 v72
      store_step with Store.apply_rep s55 v73 v2 _ _ hinv55 h64 h_v73 h_v2 (by ns_tac) (by ns_tac) as ⟨v74, s56, hinv56, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping h_v73 v73
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s56 0#u32 (0) (by scalar_tac) hinv56 h64 as ⟨v75, s57, hinv57, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v74 dropping
      store_step with Store.apply_rep s57 v74 v75 _ _ hinv57 h64 h_v74 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s58, hinv58, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping h_v74 h_v75 v74 v75
      step as ⟨e_v77, he_v77⟩
      store_step with CtorSpec.eo__2d.construct s58 e_v77 (by rw [he_v77]; exact empty_args) hinv58 h64 as ⟨v77, s59, hinv59, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v76 dropping he_v77 e_v77
      step as ⟨e_v78, he_v78⟩
      store_step with CtorSpec.eo_str_2elen.construct s59 e_v78 (by rw [he_v78]; exact empty_args) hinv59 h64 as ⟨v78, s60, hinv60, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v76 h_v77 dropping he_v78 e_v78
      store_step with Store.apply_rep s60 v78 v8 _ _ hinv60 h64 h_v78 h_v8 (by ns_tac) (by ns_tac) as ⟨v79, s61, hinv61, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v76 h_v77 dropping h_v78 v78
      store_step with Store.apply_rep s61 v77 v79 _ _ hinv61 h64 h_v77 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s62, hinv62, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v76 dropping h_v77 h_v79 v77 v79
      store_step with Store.apply_rep s62 v80 v5 _ _ hinv62 h64 h_v80 h_v5 (by ns_tac) (by ns_tac) as ⟨v81, s63, hinv63, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 h_v76 dropping h_v80 v80
      store_step with Store.apply_rep s63 v76 v81 _ _ hinv63 h64 h_v76 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s64, hinv64, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping h_v76 h_v81 v76 v81
      ite_done hinv64 hG with (eo_ite_false_rep _ hx_73 h_v82)
    · ite_branch hbv_73
      ite_stuck hinv54 hG with hx_73)
  store_step with h_ite_v83 as ⟨v83, s55, hinv55, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 h_v69 dropping h_ite_v83 h_v72 hinv54 s54 v72
  store_step with Store.apply_mk_rep s55 v69 v83 _ _ hinv55 h64 h_v69 h_v83 as ⟨v84, s56, hinv56, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v68 dropping h_v69 h_v83 hinv55 s55 v69 v83
  store_step with Store.apply_mk_rep s56 v68 v84 _ _ hinv56 h64 h_v68 h_v84 as ⟨v85, s57, hinv57, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 dropping h_v68 h_v84 hinv56 s56 v68 v84
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s57 0#u32 (0) (by scalar_tac) hinv57 h64 as ⟨v86, s58, hinv58, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 h_v85 dropping hinv57 s57
  store_step with Store.apply_mk_rep s58 v85 v86 _ _ hinv58 h64 h_v85 h_v86 as ⟨v87, s59, hinv59, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 h_v67 dropping h_v85 h_v86 hinv58 s58 v85 v86
  store_step with Store.apply_mk_rep s59 v67 v87 _ _ hinv59 h64 h_v67 h_v87 as ⟨v88, s60, hinv60, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v65 dropping h_v67 h_v87 hinv59 s59 v67 v87
  store_step with Store.apply_mk_rep s60 v65 v88 _ _ hinv60 h64 h_v65 h_v88 as ⟨v89, s61, hinv61, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 dropping h_v65 h_v88 hinv60 s60 v65 v88
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo__2d.construct s61 e_v90 (by rw [he_v90]; exact empty_args) hinv61 h64 as ⟨v90, s62, hinv62, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 dropping he_v90 hinv61 e_v90 s61
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_str_2elen.construct s62 e_v91 (by rw [he_v91]; exact empty_args) hinv62 h64 as ⟨v91, s63, hinv63, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v90 dropping he_v91 hinv62 e_v91 s62
  store_step with Store.apply_rep s63 v91 v8 _ _ hinv63 h64 h_v91 h_v8 (by ns_tac) (by ns_tac) as ⟨v92, s64, hinv64, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v90 dropping h_v91 hinv63 s63 v91
  store_step with Store.apply_rep s64 v90 v92 _ _ hinv64 h64 h_v90 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s65, hinv65, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 dropping h_v90 h_v92 hinv64 s64 v90 v92
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo__2b.construct s65 e_v94 (by rw [he_v94]; exact empty_args) hinv65 h64 as ⟨v94, s66, hinv66, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 dropping he_v94 hinv65 e_v94 s65
  store_step with Store.apply_rep s66 v94 v5 _ _ hinv66 h64 h_v94 h_v5 (by ns_tac) (by ns_tac) as ⟨v95, s67, hinv67, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 dropping h_v94 hinv66 s66 v94
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo__2b.construct s67 e_v96 (by rw [he_v96]; exact empty_args) hinv67 h64 as ⟨v96, s68, hinv68, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 dropping he_v96 hinv67 e_v96 s67
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_str_2elen.construct s68 e_v97 (by rw [he_v97]; exact empty_args) hinv68 h64 as ⟨v97, s69, hinv69, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 dropping he_v97 hinv68 e_v97 s68
  store_step with ih.eo__24str_5fvalue_5flen s69 v2 _ hinv69 h64 (hG.rem hrem) h_v2 as ⟨v98, s70, hinv70, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping hinv69 s69
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s70 1#u32 (1) (by scalar_tac) hinv70 h64 as ⟨v99, s71, hinv71, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v98 dropping hinv70 s70
  step as ⟨e_v100, he_v100⟩
  store_step with Store.builtin_spec_is_eq s71 e_v100 (by rw [he_v100]; rfl) h_v98 h_v99 hinv71 h64 as ⟨v100, s72, hinv72, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping h_v98 h_v99 he_v100 hinv71 e_v100 s71 v98 v99
  have h_ite_v111 := (show if_142_eo__24str_5freduction_5fpred s72 v100 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s72.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_142_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s72
    rcases Store.boolean_value_term h_v100 with ⟨hx_101, hbv_101⟩ | ⟨hx_101, hbv_101⟩ | ⟨hx_101, hbv_101⟩
    · ite_branch hbv_101
      ite_done hinv72 hG with (eo_ite_true_rep _ hx_101 h_v2)
    · ite_branch hbv_101
      step as ⟨e_v101, he_v101⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s72 e_v101 (by rw [he_v101]; exact empty_args) hinv72 h64 as ⟨v101, s73, hinv73, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping h_v100 he_v101 e_v101 v100
      store_step with Store.apply_rep s73 v101 v2 _ _ hinv73 h64 h_v101 h_v2 (by ns_tac) (by ns_tac) as ⟨v102, s74, hinv74, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping h_v101 v101
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s74 0#u32 (0) (by scalar_tac) hinv74 h64 as ⟨v103, s75, hinv75, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v102 dropping
      store_step with Store.apply_rep s75 v102 v103 _ _ hinv75 h64 h_v102 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s76, hinv76, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping h_v102 h_v103 v102 v103
      step as ⟨e_v105, he_v105⟩
      store_step with CtorSpec.eo__2d.construct s76 e_v105 (by rw [he_v105]; exact empty_args) hinv76 h64 as ⟨v105, s77, hinv77, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v104 dropping he_v105 e_v105
      step as ⟨e_v106, he_v106⟩
      store_step with CtorSpec.eo_str_2elen.construct s77 e_v106 (by rw [he_v106]; exact empty_args) hinv77 h64 as ⟨v106, s78, hinv78, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v104 h_v105 dropping he_v106 e_v106
      store_step with Store.apply_rep s78 v106 v8 _ _ hinv78 h64 h_v106 h_v8 (by ns_tac) (by ns_tac) as ⟨v107, s79, hinv79, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v104 h_v105 dropping h_v106 v106
      store_step with Store.apply_rep s79 v105 v107 _ _ hinv79 h64 h_v105 h_v107 (by ns_tac) (by ns_tac) as ⟨v108, s80, hinv80, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v104 dropping h_v105 h_v107 v105 v107
      store_step with Store.apply_rep s80 v108 v5 _ _ hinv80 h64 h_v108 h_v5 (by ns_tac) (by ns_tac) as ⟨v109, s81, hinv81, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 h_v104 dropping h_v108 v108
      store_step with Store.apply_rep s81 v104 v109 _ _ hinv81 h64 h_v104 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s82, hinv82, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping h_v104 h_v109 v104 v109
      ite_done hinv82 hG with (eo_ite_false_rep _ hx_101 h_v110)
    · ite_branch hbv_101
      ite_stuck hinv72 hG with hx_101)
  store_step with h_ite_v111 as ⟨v111, s73, hinv73, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 h_v97 dropping h_ite_v111 h_v100 hinv72 s72 v100
  store_step with Store.apply_mk_rep s73 v97 v111 _ _ hinv73 h64 h_v97 h_v111 as ⟨v112, s74, hinv74, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v96 dropping h_v111 h_v97 hinv73 s73 v111 v97
  store_step with Store.apply_mk_rep s74 v96 v112 _ _ hinv74 h64 h_v96 h_v112 as ⟨v113, s75, hinv75, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 dropping h_v112 h_v96 hinv74 s74 v112 v96
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s75 0#u32 (0) (by scalar_tac) hinv75 h64 as ⟨v114, s76, hinv76, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 h_v113 dropping hinv75 s75
  store_step with Store.apply_mk_rep s76 v113 v114 _ _ hinv76 h64 h_v113 h_v114 as ⟨v115, s77, hinv77, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 h_v95 dropping h_v113 h_v114 hinv76 s76 v113 v114
  store_step with Store.apply_mk_rep s77 v95 v115 _ _ hinv77 h64 h_v95 h_v115 as ⟨v116, s78, hinv78, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 h_v93 dropping h_v115 h_v95 hinv77 s77 v115 v95
  store_step with Store.apply_mk_rep s78 v93 v116 _ _ hinv78 h64 h_v93 h_v116 as ⟨v117, s79, hinv79, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 h_v89 dropping h_v116 h_v93 hinv78 s78 v116 v93
  store_step with Store.apply_mk_rep s79 v89 v117 _ _ hinv79 h64 h_v89 h_v117 as ⟨v118, s80, hinv80, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 h_v63 dropping h_v117 h_v89 hinv79 s79 v117 v89
  store_step with Store.apply_mk_rep s80 v63 v118 _ _ hinv80 h64 h_v63 h_v118 as ⟨v119, s81, hinv81, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v62 dropping h_v118 h_v63 hinv80 s80 v118 v63
  store_step with Store.apply_mk_rep s81 v62 v119 _ _ hinv81 h64 h_v62 h_v119 as ⟨v120, s82, hinv82, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 dropping h_v119 h_v62 hinv81 s81 v119 v62
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s82 e_v121 (by rw [he_v121]; exact empty_args) hinv82 h64 as ⟨v121, s83, hinv83, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 dropping he_v121 hinv82 e_v121 s82
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo__40purify.construct s83 e_v122 (by rw [he_v122]; exact empty_args) hinv83 h64 as ⟨v122, s84, hinv84, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 dropping he_v122 hinv83 e_v122 s83
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s84 e_v123 (by rw [he_v123]; exact empty_args) hinv84 h64 as ⟨v123, s85, hinv85, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 h_v122 dropping he_v123 hinv84 e_v123 s84
  store_step with Store.apply_rep s85 v123 v8 _ _ hinv85 h64 h_v123 h_v8 (by ns_tac) (by ns_tac) as ⟨v124, s86, hinv86, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 h_v122 dropping h_v123 hinv85 s85 v123
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s86 0#u32 (0) (by scalar_tac) hinv86 h64 as ⟨v125, s87, hinv87, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 h_v122 h_v124 dropping hinv86 s86
  store_step with Store.apply_rep s87 v124 v125 _ _ hinv87 h64 h_v124 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s88, hinv88, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 h_v122 dropping h_v124 h_v125 hinv87 s87 v124 v125
  store_step with Store.apply_rep s88 v126 v5 _ _ hinv88 h64 h_v126 h_v5 (by ns_tac) (by ns_tac) as ⟨v127, s89, hinv89, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 h_v122 dropping h_v126 hinv88 s88 v126
  store_step with Store.apply_rep s89 v122 v127 _ _ hinv89 h64 h_v122 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s90, hinv90, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 dropping h_v122 h_v127 hinv89 s89 v122 v127
  store_step with ih.eo__24eo_5ftypeof s90 v128 _ hinv90 h64 (hG.rem hrem) h_v128 as ⟨v129, s91, hinv91, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 h_v121 dropping h_v128 hinv90 s90 v128
  store_step with ih.eo__24eo_5fnil s91 v121 v129 _ _ hinv91 h64 (hG.rem hrem) h_v121 h_v129 as ⟨v130, s92, hinv92, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 h_v120 dropping h_v121 h_v129 hinv91 s91 v121 v129
  store_step with Store.apply_mk_rep s92 v120 v130 _ _ hinv92 h64 h_v120 h_v130 as ⟨v131, s93, hinv93, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 h_v61 dropping h_v120 h_v130 hinv92 s92 v120 v130
  store_step with Store.apply_mk_rep s93 v61 v131 _ _ hinv93 h64 h_v61 h_v131 as ⟨v132, s94, hinv94, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 h_v45 dropping h_v131 h_v61 hinv93 s93 v131 v61
  store_step with Store.apply_mk_rep s94 v45 v132 _ _ hinv94 h64 h_v45 h_v132 as ⟨v133, s95, hinv95, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 h_v36 dropping h_v132 h_v45 hinv94 s94 v132 v45
  store_step with Store.apply_mk_rep s95 v36 v133 _ _ hinv95 h64 h_v36 h_v133 as ⟨v134, s96, hinv96, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v28 dropping h_v133 h_v36 hinv95 s95 v133 v36
  store_step with Store.apply_mk_rep s96 v28 v134 _ _ hinv96 h64 h_v28 h_v134 as ⟨v135, s97, hinv97, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 dropping h_v134 h_v28 hinv96 s96 v134 v28
  step as ⟨e_v136, he_v136⟩
  store_step with CtorSpec.eo_and.construct s97 e_v136 (by rw [he_v136]; exact empty_args) hinv97 h64 as ⟨v136, s98, hinv98, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 dropping he_v136 hinv97 e_v136 s97
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo__3d.construct s98 e_v137 (by rw [he_v137]; exact empty_args) hinv98 h64 as ⟨v137, s99, hinv99, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 dropping he_v137 hinv98 e_v137 s98
  store_step with Store.apply_rep s99 v137 v8 _ _ hinv99 h64 h_v137 h_v8 (by ns_tac) (by ns_tac) as ⟨v138, s100, hinv100, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 dropping h_v137 hinv99 s99 v137
  step as ⟨e_v139, he_v139⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s100 e_v139 (by rw [he_v139]; exact empty_args) hinv100 h64 as ⟨v139, s101, hinv101, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 dropping he_v139 hinv100 e_v139 s100
  step as ⟨e_v140, he_v140⟩
  store_step with CtorSpec.eo__40purify.construct s101 e_v140 (by rw [he_v140]; exact empty_args) hinv101 h64 as ⟨v140, s102, hinv102, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 dropping he_v140 hinv101 e_v140 s101
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s102 e_v141 (by rw [he_v141]; exact empty_args) hinv102 h64 as ⟨v141, s103, hinv103, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 h_v140 dropping he_v141 hinv102 e_v141 s102
  store_step with Store.apply_rep s103 v141 v8 _ _ hinv103 h64 h_v141 h_v8 (by ns_tac) (by ns_tac) as ⟨v142, s104, hinv104, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 h_v140 dropping h_v141 hinv103 s103 v141
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s104 0#u32 (0) (by scalar_tac) hinv104 h64 as ⟨v143, s105, hinv105, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 h_v140 h_v142 dropping hinv104 s104
  store_step with Store.apply_rep s105 v142 v143 _ _ hinv105 h64 h_v142 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s106, hinv106, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 h_v140 dropping h_v142 h_v143 hinv105 s105 v142 v143
  store_step with Store.apply_rep s106 v144 v5 _ _ hinv106 h64 h_v144 h_v5 (by ns_tac) (by ns_tac) as ⟨v145, s107, hinv107, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 h_v140 dropping h_v144 hinv106 s106 v144
  store_step with Store.apply_rep s107 v140 v145 _ _ hinv107 h64 h_v140 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s108, hinv108, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v139 dropping h_v140 h_v145 hinv107 s107 v140 v145
  store_step with Store.apply_rep s108 v139 v146 _ _ hinv108 h64 h_v139 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s109, hinv109, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 dropping h_v139 h_v146 hinv108 s108 v139 v146
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s109 e_v148 (by rw [he_v148]; exact empty_args) hinv109 h64 as ⟨v148, s110, hinv110, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 dropping he_v148 hinv109 e_v148 s109
  step as ⟨e_v149, he_v149⟩
  store_step with CtorSpec.eo__40purify.construct s110 e_v149 (by rw [he_v149]; exact empty_args) hinv110 h64 as ⟨v149, s111, hinv111, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 dropping he_v149 hinv110 e_v149 s110
  step as ⟨e_v150, he_v150⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s111 e_v150 (by rw [he_v150]; exact empty_args) hinv111 h64 as ⟨v150, s112, hinv112, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 dropping he_v150 hinv111 e_v150 s111
  store_step with Store.apply_rep s112 v150 v8 _ _ hinv112 h64 h_v150 h_v8 (by ns_tac) (by ns_tac) as ⟨v151, s113, hinv113, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 dropping h_v150 hinv112 s112 v150
  store_step with Store.apply_rep s113 v151 v5 _ _ hinv113 h64 h_v151 h_v5 (by ns_tac) (by ns_tac) as ⟨v152, s114, hinv114, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 dropping h_v151 hinv113 s113 v151
  step as ⟨e_v153, he_v153⟩
  store_step with CtorSpec.eo_str_2elen.construct s114 e_v153 (by rw [he_v153]; exact empty_args) hinv114 h64 as ⟨v153, s115, hinv115, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 dropping he_v153 hinv114 e_v153 s114
  store_step with ih.eo__24str_5fvalue_5flen s115 v2 _ hinv115 h64 (hG.rem hrem) h_v2 as ⟨v154, s116, hinv116, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping hinv115 s115
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s116 1#u32 (1) (by scalar_tac) hinv116 h64 as ⟨v155, s117, hinv117, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v154 dropping hinv116 s116
  step as ⟨e_v156, he_v156⟩
  store_step with Store.builtin_spec_is_eq s117 e_v156 (by rw [he_v156]; rfl) h_v154 h_v155 hinv117 h64 as ⟨v156, s118, hinv118, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping h_v154 h_v155 he_v156 hinv117 e_v156 s117 v154 v155
  have h_ite_v167 := (show if_143_eo__24str_5freduction_5fpred s118 v156 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s118.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_143_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s118
    rcases Store.boolean_value_term h_v156 with ⟨hx_157, hbv_157⟩ | ⟨hx_157, hbv_157⟩ | ⟨hx_157, hbv_157⟩
    · ite_branch hbv_157
      ite_done hinv118 hG with (eo_ite_true_rep _ hx_157 h_v2)
    · ite_branch hbv_157
      step as ⟨e_v157, he_v157⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s118 e_v157 (by rw [he_v157]; exact empty_args) hinv118 h64 as ⟨v157, s119, hinv119, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping h_v156 he_v157 e_v157 v156
      store_step with Store.apply_rep s119 v157 v2 _ _ hinv119 h64 h_v157 h_v2 (by ns_tac) (by ns_tac) as ⟨v158, s120, hinv120, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping h_v157 v157
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s120 0#u32 (0) (by scalar_tac) hinv120 h64 as ⟨v159, s121, hinv121, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v158 dropping
      store_step with Store.apply_rep s121 v158 v159 _ _ hinv121 h64 h_v158 h_v159 (by ns_tac) (by ns_tac) as ⟨v160, s122, hinv122, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping h_v158 h_v159 v158 v159
      step as ⟨e_v161, he_v161⟩
      store_step with CtorSpec.eo__2d.construct s122 e_v161 (by rw [he_v161]; exact empty_args) hinv122 h64 as ⟨v161, s123, hinv123, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v160 dropping he_v161 e_v161
      step as ⟨e_v162, he_v162⟩
      store_step with CtorSpec.eo_str_2elen.construct s123 e_v162 (by rw [he_v162]; exact empty_args) hinv123 h64 as ⟨v162, s124, hinv124, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v160 h_v161 dropping he_v162 e_v162
      store_step with Store.apply_rep s124 v162 v8 _ _ hinv124 h64 h_v162 h_v8 (by ns_tac) (by ns_tac) as ⟨v163, s125, hinv125, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v160 h_v161 dropping h_v162 v162
      store_step with Store.apply_rep s125 v161 v163 _ _ hinv125 h64 h_v161 h_v163 (by ns_tac) (by ns_tac) as ⟨v164, s126, hinv126, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v160 dropping h_v161 h_v163 v161 v163
      store_step with Store.apply_rep s126 v164 v5 _ _ hinv126 h64 h_v164 h_v5 (by ns_tac) (by ns_tac) as ⟨v165, s127, hinv127, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 h_v160 dropping h_v164 v164
      store_step with Store.apply_rep s127 v160 v165 _ _ hinv127 h64 h_v160 h_v165 (by ns_tac) (by ns_tac) as ⟨v166, s128, hinv128, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping h_v160 h_v165 v160 v165
      ite_done hinv128 hG with (eo_ite_false_rep _ hx_157 h_v166)
    · ite_branch hbv_157
      ite_stuck hinv118 hG with hx_157)
  store_step with h_ite_v167 as ⟨v167, s119, hinv119, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 h_v153 dropping h_ite_v167 h_v156 hinv118 s118 v156
  store_step with Store.apply_mk_rep s119 v153 v167 _ _ hinv119 h64 h_v153 h_v167 as ⟨v168, s120, hinv120, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 h_v152 dropping h_v153 h_v167 hinv119 s119 v153 v167
  store_step with Store.apply_mk_rep s120 v152 v168 _ _ hinv120 h64 h_v152 h_v168 as ⟨v169, s121, hinv121, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 h_v149 dropping h_v152 h_v168 hinv120 s120 v152 v168
  store_step with Store.apply_mk_rep s121 v149 v169 _ _ hinv121 h64 h_v149 h_v169 as ⟨v170, s122, hinv122, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v148 dropping h_v149 h_v169 hinv121 s121 v149 v169
  store_step with Store.apply_mk_rep s122 v148 v170 _ _ hinv122 h64 h_v148 h_v170 as ⟨v171, s123, hinv123, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 dropping h_v148 h_v170 hinv122 s122 v148 v170
  step as ⟨e_v172, he_v172⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s123 e_v172 (by rw [he_v172]; exact empty_args) hinv123 h64 as ⟨v172, s124, hinv124, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 dropping he_v172 hinv123 e_v172 s123
  step as ⟨e_v173, he_v173⟩
  store_step with CtorSpec.eo__40purify.construct s124 e_v173 (by rw [he_v173]; exact empty_args) hinv124 h64 as ⟨v173, s125, hinv125, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 dropping he_v173 hinv124 e_v173 s124
  step as ⟨e_v174, he_v174⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s125 e_v174 (by rw [he_v174]; exact empty_args) hinv125 h64 as ⟨v174, s126, hinv126, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 dropping he_v174 hinv125 e_v174 s125
  store_step with Store.apply_rep s126 v174 v8 _ _ hinv126 h64 h_v174 h_v8 (by ns_tac) (by ns_tac) as ⟨v175, s127, hinv127, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 dropping h_v174 hinv126 s126 v174
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo__2b.construct s127 e_v176 (by rw [he_v176]; exact empty_args) hinv127 h64 as ⟨v176, s128, hinv128, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 dropping he_v176 hinv127 e_v176 s127
  store_step with Store.apply_rep s128 v176 v5 _ _ hinv128 h64 h_v176 h_v5 (by ns_tac) (by ns_tac) as ⟨v177, s129, hinv129, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 dropping h_v176 hinv128 s128 v176
  step as ⟨e_v178, he_v178⟩
  store_step with CtorSpec.eo__2b.construct s129 e_v178 (by rw [he_v178]; exact empty_args) hinv129 h64 as ⟨v178, s130, hinv130, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 dropping he_v178 hinv129 e_v178 s129
  step as ⟨e_v179, he_v179⟩
  store_step with CtorSpec.eo_str_2elen.construct s130 e_v179 (by rw [he_v179]; exact empty_args) hinv130 h64 as ⟨v179, s131, hinv131, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 dropping he_v179 hinv130 e_v179 s130
  store_step with ih.eo__24str_5fvalue_5flen s131 v2 _ hinv131 h64 (hG.rem hrem) h_v2 as ⟨v180, s132, hinv132, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping hinv131 s131
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s132 1#u32 (1) (by scalar_tac) hinv132 h64 as ⟨v181, s133, hinv133, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v180 dropping hinv132 s132
  step as ⟨e_v182, he_v182⟩
  store_step with Store.builtin_spec_is_eq s133 e_v182 (by rw [he_v182]; rfl) h_v180 h_v181 hinv133 h64 as ⟨v182, s134, hinv134, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping h_v180 h_v181 he_v182 hinv133 e_v182 s133 v180 v181
  have h_ite_v193 := (show if_144_eo__24str_5freduction_5fpred s134 v182 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s134.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_144_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s134
    rcases Store.boolean_value_term h_v182 with ⟨hx_183, hbv_183⟩ | ⟨hx_183, hbv_183⟩ | ⟨hx_183, hbv_183⟩
    · ite_branch hbv_183
      ite_done hinv134 hG with (eo_ite_true_rep _ hx_183 h_v2)
    · ite_branch hbv_183
      step as ⟨e_v183, he_v183⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s134 e_v183 (by rw [he_v183]; exact empty_args) hinv134 h64 as ⟨v183, s135, hinv135, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping h_v182 he_v183 e_v183 v182
      store_step with Store.apply_rep s135 v183 v2 _ _ hinv135 h64 h_v183 h_v2 (by ns_tac) (by ns_tac) as ⟨v184, s136, hinv136, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping h_v183 v183
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s136 0#u32 (0) (by scalar_tac) hinv136 h64 as ⟨v185, s137, hinv137, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v184 dropping
      store_step with Store.apply_rep s137 v184 v185 _ _ hinv137 h64 h_v184 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s138, hinv138, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping h_v184 h_v185 v184 v185
      step as ⟨e_v187, he_v187⟩
      store_step with CtorSpec.eo__2d.construct s138 e_v187 (by rw [he_v187]; exact empty_args) hinv138 h64 as ⟨v187, s139, hinv139, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v186 dropping he_v187 e_v187
      step as ⟨e_v188, he_v188⟩
      store_step with CtorSpec.eo_str_2elen.construct s139 e_v188 (by rw [he_v188]; exact empty_args) hinv139 h64 as ⟨v188, s140, hinv140, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v186 h_v187 dropping he_v188 e_v188
      store_step with Store.apply_rep s140 v188 v8 _ _ hinv140 h64 h_v188 h_v8 (by ns_tac) (by ns_tac) as ⟨v189, s141, hinv141, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v186 h_v187 dropping h_v188 v188
      store_step with Store.apply_rep s141 v187 v189 _ _ hinv141 h64 h_v187 h_v189 (by ns_tac) (by ns_tac) as ⟨v190, s142, hinv142, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v186 dropping h_v187 h_v189 v187 v189
      store_step with Store.apply_rep s142 v190 v5 _ _ hinv142 h64 h_v190 h_v5 (by ns_tac) (by ns_tac) as ⟨v191, s143, hinv143, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 h_v186 dropping h_v190 v190
      store_step with Store.apply_rep s143 v186 v191 _ _ hinv143 h64 h_v186 h_v191 (by ns_tac) (by ns_tac) as ⟨v192, s144, hinv144, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping h_v186 h_v191 v186 v191
      ite_done hinv144 hG with (eo_ite_false_rep _ hx_183 h_v192)
    · ite_branch hbv_183
      ite_stuck hinv134 hG with hx_183)
  store_step with h_ite_v193 as ⟨v193, s135, hinv135, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 h_v179 dropping h_ite_v193 h_v182 hinv134 s134 v182
  store_step with Store.apply_mk_rep s135 v179 v193 _ _ hinv135 h64 h_v179 h_v193 as ⟨v194, s136, hinv136, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v178 dropping h_v179 h_v193 hinv135 s135 v179 v193
  store_step with Store.apply_mk_rep s136 v178 v194 _ _ hinv136 h64 h_v178 h_v194 as ⟨v195, s137, hinv137, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 dropping h_v178 h_v194 hinv136 s136 v178 v194
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s137 0#u32 (0) (by scalar_tac) hinv137 h64 as ⟨v196, s138, hinv138, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 h_v195 dropping hinv137 s137
  store_step with Store.apply_mk_rep s138 v195 v196 _ _ hinv138 h64 h_v195 h_v196 as ⟨v197, s139, hinv139, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 h_v177 dropping h_v195 h_v196 hinv138 s138 v195 v196
  store_step with Store.apply_mk_rep s139 v177 v197 _ _ hinv139 h64 h_v177 h_v197 as ⟨v198, s140, hinv140, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v175 dropping h_v177 h_v197 hinv139 s139 v177 v197
  store_step with Store.apply_mk_rep s140 v175 v198 _ _ hinv140 h64 h_v175 h_v198 as ⟨v199, s141, hinv141, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 dropping h_v175 h_v198 hinv140 s140 v175 v198
  step as ⟨e_v200, he_v200⟩
  store_step with CtorSpec.eo__2d.construct s141 e_v200 (by rw [he_v200]; exact empty_args) hinv141 h64 as ⟨v200, s142, hinv142, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 dropping he_v200 hinv141 e_v200 s141
  step as ⟨e_v201, he_v201⟩
  store_step with CtorSpec.eo_str_2elen.construct s142 e_v201 (by rw [he_v201]; exact empty_args) hinv142 h64 as ⟨v201, s143, hinv143, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v200 dropping he_v201 hinv142 e_v201 s142
  store_step with Store.apply_rep s143 v201 v8 _ _ hinv143 h64 h_v201 h_v8 (by ns_tac) (by ns_tac) as ⟨v202, s144, hinv144, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v200 dropping h_v201 hinv143 s143 v201
  store_step with Store.apply_rep s144 v200 v202 _ _ hinv144 h64 h_v200 h_v202 (by ns_tac) (by ns_tac) as ⟨v203, s145, hinv145, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 dropping h_v200 h_v202 hinv144 s144 v200 v202
  step as ⟨e_v204, he_v204⟩
  store_step with CtorSpec.eo__2b.construct s145 e_v204 (by rw [he_v204]; exact empty_args) hinv145 h64 as ⟨v204, s146, hinv146, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 dropping he_v204 hinv145 e_v204 s145
  store_step with Store.apply_rep s146 v204 v5 _ _ hinv146 h64 h_v204 h_v5 (by ns_tac) (by ns_tac) as ⟨v205, s147, hinv147, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 dropping h_v204 hinv146 s146 v204
  step as ⟨e_v206, he_v206⟩
  store_step with CtorSpec.eo__2b.construct s147 e_v206 (by rw [he_v206]; exact empty_args) hinv147 h64 as ⟨v206, s148, hinv148, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 dropping he_v206 hinv147 e_v206 s147
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo_str_2elen.construct s148 e_v207 (by rw [he_v207]; exact empty_args) hinv148 h64 as ⟨v207, s149, hinv149, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 dropping he_v207 hinv148 e_v207 s148
  store_step with ih.eo__24str_5fvalue_5flen s149 v2 _ hinv149 h64 (hG.rem hrem) h_v2 as ⟨v208, s150, hinv150, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping hinv149 s149
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s150 1#u32 (1) (by scalar_tac) hinv150 h64 as ⟨v209, s151, hinv151, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v208 dropping hinv150 s150
  step as ⟨e_v210, he_v210⟩
  store_step with Store.builtin_spec_is_eq s151 e_v210 (by rw [he_v210]; rfl) h_v208 h_v209 hinv151 h64 as ⟨v210, s152, hinv152, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping h_v208 h_v209 he_v210 hinv151 e_v210 s151 v208 v209
  have h_ite_v221 := (show if_145_eo__24str_5freduction_5fpred s152 v210 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s152.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_145_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s152
    rcases Store.boolean_value_term h_v210 with ⟨hx_211, hbv_211⟩ | ⟨hx_211, hbv_211⟩ | ⟨hx_211, hbv_211⟩
    · ite_branch hbv_211
      ite_done hinv152 hG with (eo_ite_true_rep _ hx_211 h_v2)
    · ite_branch hbv_211
      step as ⟨e_v211, he_v211⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s152 e_v211 (by rw [he_v211]; exact empty_args) hinv152 h64 as ⟨v211, s153, hinv153, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping h_v210 he_v211 e_v211 v210
      store_step with Store.apply_rep s153 v211 v2 _ _ hinv153 h64 h_v211 h_v2 (by ns_tac) (by ns_tac) as ⟨v212, s154, hinv154, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping h_v211 v211
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s154 0#u32 (0) (by scalar_tac) hinv154 h64 as ⟨v213, s155, hinv155, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v212 dropping
      store_step with Store.apply_rep s155 v212 v213 _ _ hinv155 h64 h_v212 h_v213 (by ns_tac) (by ns_tac) as ⟨v214, s156, hinv156, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping h_v212 h_v213 v212 v213
      step as ⟨e_v215, he_v215⟩
      store_step with CtorSpec.eo__2d.construct s156 e_v215 (by rw [he_v215]; exact empty_args) hinv156 h64 as ⟨v215, s157, hinv157, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v214 dropping he_v215 e_v215
      step as ⟨e_v216, he_v216⟩
      store_step with CtorSpec.eo_str_2elen.construct s157 e_v216 (by rw [he_v216]; exact empty_args) hinv157 h64 as ⟨v216, s158, hinv158, h_v216⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v214 h_v215 dropping he_v216 e_v216
      store_step with Store.apply_rep s158 v216 v8 _ _ hinv158 h64 h_v216 h_v8 (by ns_tac) (by ns_tac) as ⟨v217, s159, hinv159, h_v217⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v214 h_v215 dropping h_v216 v216
      store_step with Store.apply_rep s159 v215 v217 _ _ hinv159 h64 h_v215 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s160, hinv160, h_v218⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v214 dropping h_v215 h_v217 v215 v217
      store_step with Store.apply_rep s160 v218 v5 _ _ hinv160 h64 h_v218 h_v5 (by ns_tac) (by ns_tac) as ⟨v219, s161, hinv161, h_v219⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 h_v214 dropping h_v218 v218
      store_step with Store.apply_rep s161 v214 v219 _ _ hinv161 h64 h_v214 h_v219 (by ns_tac) (by ns_tac) as ⟨v220, s162, hinv162, h_v220⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping h_v214 h_v219 v214 v219
      ite_done hinv162 hG with (eo_ite_false_rep _ hx_211 h_v220)
    · ite_branch hbv_211
      ite_stuck hinv152 hG with hx_211)
  store_step with h_ite_v221 as ⟨v221, s153, hinv153, h_v221⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 h_v207 dropping h_ite_v221 h_v210 hinv152 s152 v210
  store_step with Store.apply_mk_rep s153 v207 v221 _ _ hinv153 h64 h_v207 h_v221 as ⟨v222, s154, hinv154, h_v222⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v206 dropping h_v207 h_v221 hinv153 s153 v207 v221
  store_step with Store.apply_mk_rep s154 v206 v222 _ _ hinv154 h64 h_v206 h_v222 as ⟨v223, s155, hinv155, h_v223⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 dropping h_v206 h_v222 hinv154 s154 v206 v222
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s155 0#u32 (0) (by scalar_tac) hinv155 h64 as ⟨v224, s156, hinv156, h_v224⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 h_v223 dropping hinv155 s155
  store_step with Store.apply_mk_rep s156 v223 v224 _ _ hinv156 h64 h_v223 h_v224 as ⟨v225, s157, hinv157, h_v225⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 h_v205 dropping h_v223 h_v224 hinv156 s156 v223 v224
  store_step with Store.apply_mk_rep s157 v205 v225 _ _ hinv157 h64 h_v205 h_v225 as ⟨v226, s158, hinv158, h_v226⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 h_v203 dropping h_v205 h_v225 hinv157 s157 v205 v225
  store_step with Store.apply_mk_rep s158 v203 v226 _ _ hinv158 h64 h_v203 h_v226 as ⟨v227, s159, hinv159, h_v227⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 h_v199 dropping h_v203 h_v226 hinv158 s158 v203 v226
  store_step with Store.apply_mk_rep s159 v199 v227 _ _ hinv159 h64 h_v199 h_v227 as ⟨v228, s160, hinv160, h_v228⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 h_v173 dropping h_v199 h_v227 hinv159 s159 v199 v227
  store_step with Store.apply_mk_rep s160 v173 v228 _ _ hinv160 h64 h_v173 h_v228 as ⟨v229, s161, hinv161, h_v229⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v172 dropping h_v173 h_v228 hinv160 s160 v173 v228
  store_step with Store.apply_mk_rep s161 v172 v229 _ _ hinv161 h64 h_v172 h_v229 as ⟨v230, s162, hinv162, h_v230⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 dropping h_v172 h_v229 hinv161 s161 v172 v229
  step as ⟨e_v231, he_v231⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s162 e_v231 (by rw [he_v231]; exact empty_args) hinv162 h64 as ⟨v231, s163, hinv163, h_v231⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 dropping he_v231 hinv162 e_v231 s162
  step as ⟨e_v232, he_v232⟩
  store_step with CtorSpec.eo__40purify.construct s163 e_v232 (by rw [he_v232]; exact empty_args) hinv163 h64 as ⟨v232, s164, hinv164, h_v232⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 dropping he_v232 hinv163 e_v232 s163
  step as ⟨e_v233, he_v233⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s164 e_v233 (by rw [he_v233]; exact empty_args) hinv164 h64 as ⟨v233, s165, hinv165, h_v233⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 h_v232 dropping he_v233 hinv164 e_v233 s164
  store_step with Store.apply_rep s165 v233 v8 _ _ hinv165 h64 h_v233 h_v8 (by ns_tac) (by ns_tac) as ⟨v234, s166, hinv166, h_v234⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 h_v232 dropping h_v233 hinv165 s165 v233
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s166 0#u32 (0) (by scalar_tac) hinv166 h64 as ⟨v235, s167, hinv167, h_v235⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 h_v232 h_v234 dropping hinv166 s166
  store_step with Store.apply_rep s167 v234 v235 _ _ hinv167 h64 h_v234 h_v235 (by ns_tac) (by ns_tac) as ⟨v236, s168, hinv168, h_v236⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 h_v232 dropping h_v234 h_v235 hinv167 s167 v234 v235
  store_step with Store.apply_rep s168 v236 v5 _ _ hinv168 h64 h_v236 h_v5 (by ns_tac) (by ns_tac) as ⟨v237, s169, hinv169, h_v237⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 h_v232 dropping h_v236 hinv168 s168 v236
  store_step with Store.apply_rep s169 v232 v237 _ _ hinv169 h64 h_v232 h_v237 (by ns_tac) (by ns_tac) as ⟨v238, s170, hinv170, h_v238⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 dropping h_v232 h_v237 hinv169 s169 v232 v237
  store_step with ih.eo__24eo_5ftypeof s170 v238 _ hinv170 h64 (hG.rem hrem) h_v238 as ⟨v239, s171, hinv171, h_v239⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 h_v231 dropping h_v238 hinv170 s170 v238
  store_step with ih.eo__24eo_5fnil s171 v231 v239 _ _ hinv171 h64 (hG.rem hrem) h_v231 h_v239 as ⟨v240, s172, hinv172, h_v240⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 h_v230 dropping h_v231 h_v239 hinv171 s171 v231 v239
  store_step with Store.apply_mk_rep s172 v230 v240 _ _ hinv172 h64 h_v230 h_v240 as ⟨v241, s173, hinv173, h_v241⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 h_v171 dropping h_v230 h_v240 hinv172 s172 v230 v240
  store_step with Store.apply_mk_rep s173 v171 v241 _ _ hinv173 h64 h_v171 h_v241 as ⟨v242, s174, hinv174, h_v242⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 h_v147 dropping h_v171 h_v241 hinv173 s173 v171 v241
  store_step with Store.apply_mk_rep s174 v147 v242 _ _ hinv174 h64 h_v147 h_v242 as ⟨v243, s175, hinv175, h_v243⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 h_v138 dropping h_v147 h_v242 hinv174 s174 v147 v242
  store_step with Store.apply_mk_rep s175 v138 v243 _ _ hinv175 h64 h_v138 h_v243 as ⟨v244, s176, hinv176, h_v244⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v136 dropping h_v138 h_v243 hinv175 s175 v138 v243
  store_step with Store.apply_mk_rep s176 v136 v244 _ _ hinv176 h64 h_v136 h_v244 as ⟨v245, s177, hinv177, h_v245⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 dropping h_v136 h_v244 hinv176 s176 v136 v244
  step as ⟨e_v246, he_v246⟩
  store_step with CtorSpec.eo_and.construct s177 e_v246 (by rw [he_v246]; exact empty_args) hinv177 h64 as ⟨v246, s178, hinv178, h_v246⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 dropping he_v246 hinv177 e_v246 s177
  step as ⟨e_v247, he_v247⟩
  store_step with CtorSpec.eo__3d.construct s178 e_v247 (by rw [he_v247]; exact empty_args) hinv178 h64 as ⟨v247, s179, hinv179, h_v247⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 dropping he_v247 hinv178 e_v247 s178
  step as ⟨e_v248, he_v248⟩
  store_step with CtorSpec.eo_str_2elen.construct s179 e_v248 (by rw [he_v248]; exact empty_args) hinv179 h64 as ⟨v248, s180, hinv180, h_v248⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 dropping he_v248 hinv179 e_v248 s179
  step as ⟨e_v249, he_v249⟩
  store_step with CtorSpec.eo__40purify.construct s180 e_v249 (by rw [he_v249]; exact empty_args) hinv180 h64 as ⟨v249, s181, hinv181, h_v249⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 dropping he_v249 hinv180 e_v249 s180
  step as ⟨e_v250, he_v250⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s181 e_v250 (by rw [he_v250]; exact empty_args) hinv181 h64 as ⟨v250, s182, hinv182, h_v250⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 h_v249 dropping he_v250 hinv181 e_v250 s181
  store_step with Store.apply_rep s182 v250 v8 _ _ hinv182 h64 h_v250 h_v8 (by ns_tac) (by ns_tac) as ⟨v251, s183, hinv183, h_v251⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 h_v249 dropping h_v250 hinv182 s182 v250
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s183 0#u32 (0) (by scalar_tac) hinv183 h64 as ⟨v252, s184, hinv184, h_v252⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 h_v249 h_v251 dropping hinv183 s183
  store_step with Store.apply_rep s184 v251 v252 _ _ hinv184 h64 h_v251 h_v252 (by ns_tac) (by ns_tac) as ⟨v253, s185, hinv185, h_v253⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 h_v249 dropping h_v251 h_v252 hinv184 s184 v251 v252
  store_step with Store.apply_rep s185 v253 v5 _ _ hinv185 h64 h_v253 h_v5 (by ns_tac) (by ns_tac) as ⟨v254, s186, hinv186, h_v254⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 h_v249 dropping h_v253 hinv185 s185 v253
  store_step with Store.apply_rep s186 v249 v254 _ _ hinv186 h64 h_v249 h_v254 (by ns_tac) (by ns_tac) as ⟨v255, s187, hinv187, h_v255⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 h_v248 dropping h_v249 h_v254 hinv186 s186 v249 v254
  store_step with Store.apply_rep s187 v248 v255 _ _ hinv187 h64 h_v248 h_v255 (by ns_tac) (by ns_tac) as ⟨v256, s188, hinv188, h_v256⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 h_v247 dropping h_v248 h_v255 hinv187 s187 v248 v255
  store_step with Store.apply_rep s188 v247 v256 _ _ hinv188 h64 h_v247 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s189, hinv189, h_v257⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 dropping h_v247 h_v256 hinv188 s188 v247 v256
  store_step with Store.apply_rep s189 v257 v5 _ _ hinv189 h64 h_v257 h_v5 (by ns_tac) (by ns_tac) as ⟨v258, s190, hinv190, h_v258⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v246 dropping h_v257 hinv189 s189 v257
  store_step with Store.apply_rep s190 v246 v258 _ _ hinv190 h64 h_v246 h_v258 (by ns_tac) (by ns_tac) as ⟨v259, s191, hinv191, h_v259⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 dropping h_v246 h_v258 hinv190 s190 v246 v258
  step as ⟨e_v260, he_v260⟩
  store_step with CtorSpec.eo_and.construct s191 e_v260 (by rw [he_v260]; exact empty_args) hinv191 h64 as ⟨v260, s192, hinv192, h_v260⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 dropping he_v260 hinv191 e_v260 s191
  step as ⟨e_v261, he_v261⟩
  store_step with CtorSpec.eo__3d.construct s192 e_v261 (by rw [he_v261]; exact empty_args) hinv192 h64 as ⟨v261, s193, hinv193, h_v261⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 dropping he_v261 hinv192 e_v261 s192
  step as ⟨e_v262, he_v262⟩
  store_step with CtorSpec.eo_str_2elen.construct s193 e_v262 (by rw [he_v262]; exact empty_args) hinv193 h64 as ⟨v262, s194, hinv194, h_v262⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 dropping he_v262 hinv193 e_v262 s193
  store_step with ih.eo__24str_5fvalue_5flen s194 v2 _ hinv194 h64 (hG.rem hrem) h_v2 as ⟨v263, s195, hinv195, h_v263⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping hinv194 s194
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s195 1#u32 (1) (by scalar_tac) hinv195 h64 as ⟨v264, s196, hinv196, h_v264⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v263 dropping hinv195 s195
  step as ⟨e_v265, he_v265⟩
  store_step with Store.builtin_spec_is_eq s196 e_v265 (by rw [he_v265]; rfl) h_v263 h_v264 hinv196 h64 as ⟨v265, s197, hinv197, h_v265⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping h_v263 h_v264 he_v265 hinv196 e_v265 s196 v263 v264
  have h_ite_v276 := (show if_146_eo__24str_5freduction_5fpred s197 v265 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s197.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_146_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s197
    rcases Store.boolean_value_term h_v265 with ⟨hx_266, hbv_266⟩ | ⟨hx_266, hbv_266⟩ | ⟨hx_266, hbv_266⟩
    · ite_branch hbv_266
      ite_done hinv197 hG with (eo_ite_true_rep _ hx_266 h_v2)
    · ite_branch hbv_266
      step as ⟨e_v266, he_v266⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s197 e_v266 (by rw [he_v266]; exact empty_args) hinv197 h64 as ⟨v266, s198, hinv198, h_v266⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping h_v265 he_v266 e_v266 v265
      store_step with Store.apply_rep s198 v266 v2 _ _ hinv198 h64 h_v266 h_v2 (by ns_tac) (by ns_tac) as ⟨v267, s199, hinv199, h_v267⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping h_v266 v266
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s199 0#u32 (0) (by scalar_tac) hinv199 h64 as ⟨v268, s200, hinv200, h_v268⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v267 dropping
      store_step with Store.apply_rep s200 v267 v268 _ _ hinv200 h64 h_v267 h_v268 (by ns_tac) (by ns_tac) as ⟨v269, s201, hinv201, h_v269⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping h_v267 h_v268 v267 v268
      step as ⟨e_v270, he_v270⟩
      store_step with CtorSpec.eo__2d.construct s201 e_v270 (by rw [he_v270]; exact empty_args) hinv201 h64 as ⟨v270, s202, hinv202, h_v270⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v269 dropping he_v270 e_v270
      step as ⟨e_v271, he_v271⟩
      store_step with CtorSpec.eo_str_2elen.construct s202 e_v271 (by rw [he_v271]; exact empty_args) hinv202 h64 as ⟨v271, s203, hinv203, h_v271⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v269 h_v270 dropping he_v271 e_v271
      store_step with Store.apply_rep s203 v271 v8 _ _ hinv203 h64 h_v271 h_v8 (by ns_tac) (by ns_tac) as ⟨v272, s204, hinv204, h_v272⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v269 h_v270 dropping h_v271 v271
      store_step with Store.apply_rep s204 v270 v272 _ _ hinv204 h64 h_v270 h_v272 (by ns_tac) (by ns_tac) as ⟨v273, s205, hinv205, h_v273⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v269 dropping h_v270 h_v272 v270 v272
      store_step with Store.apply_rep s205 v273 v5 _ _ hinv205 h64 h_v273 h_v5 (by ns_tac) (by ns_tac) as ⟨v274, s206, hinv206, h_v274⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 h_v269 dropping h_v273 v273
      store_step with Store.apply_rep s206 v269 v274 _ _ hinv206 h64 h_v269 h_v274 (by ns_tac) (by ns_tac) as ⟨v275, s207, hinv207, h_v275⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping h_v269 h_v274 v269 v274
      ite_done hinv207 hG with (eo_ite_false_rep _ hx_266 h_v275)
    · ite_branch hbv_266
      ite_stuck hinv197 hG with hx_266)
  store_step with h_ite_v276 as ⟨v276, s198, hinv198, h_v276⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 h_v262 dropping h_ite_v276 h_v265 hinv197 s197 v265
  store_step with Store.apply_mk_rep s198 v262 v276 _ _ hinv198 h64 h_v262 h_v276 as ⟨v277, s199, hinv199, h_v277⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v261 dropping h_v262 h_v276 hinv198 s198 v262 v276
  store_step with Store.apply_mk_rep s199 v261 v277 _ _ hinv199 h64 h_v261 h_v277 as ⟨v278, s200, hinv200, h_v278⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 dropping h_v261 h_v277 hinv199 s199 v261 v277
  step as ⟨e_v279, he_v279⟩
  store_step with CtorSpec.eo_str_2elen.construct s200 e_v279 (by rw [he_v279]; exact empty_args) hinv200 h64 as ⟨v279, s201, hinv201, h_v279⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 dropping he_v279 hinv200 e_v279 s200
  step as ⟨e_v280, he_v280⟩
  store_step with CtorSpec.eo__40purify.construct s201 e_v280 (by rw [he_v280]; exact empty_args) hinv201 h64 as ⟨v280, s202, hinv202, h_v280⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 dropping he_v280 hinv201 e_v280 s201
  step as ⟨e_v281, he_v281⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s202 e_v281 (by rw [he_v281]; exact empty_args) hinv202 h64 as ⟨v281, s203, hinv203, h_v281⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 dropping he_v281 hinv202 e_v281 s202
  store_step with Store.apply_rep s203 v281 v8 _ _ hinv203 h64 h_v281 h_v8 (by ns_tac) (by ns_tac) as ⟨v282, s204, hinv204, h_v282⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 dropping h_v281 hinv203 s203 v281
  store_step with Store.apply_rep s204 v282 v5 _ _ hinv204 h64 h_v282 h_v5 (by ns_tac) (by ns_tac) as ⟨v283, s205, hinv205, h_v283⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 dropping h_v282 hinv204 s204 v282
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo_str_2elen.construct s205 e_v284 (by rw [he_v284]; exact empty_args) hinv205 h64 as ⟨v284, s206, hinv206, h_v284⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 dropping he_v284 hinv205 e_v284 s205
  store_step with ih.eo__24str_5fvalue_5flen s206 v2 _ hinv206 h64 (hG.rem hrem) h_v2 as ⟨v285, s207, hinv207, h_v285⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping hinv206 s206
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s207 1#u32 (1) (by scalar_tac) hinv207 h64 as ⟨v286, s208, hinv208, h_v286⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v285 dropping hinv207 s207
  step as ⟨e_v287, he_v287⟩
  store_step with Store.builtin_spec_is_eq s208 e_v287 (by rw [he_v287]; rfl) h_v285 h_v286 hinv208 h64 as ⟨v287, s209, hinv209, h_v287⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping h_v285 h_v286 he_v287 hinv208 e_v287 s208 v285 v286
  have h_ite_v298 := (show if_147_eo__24str_5freduction_5fpred s209 v287 v2 v8 v5 ⦃ r s' => s'.Inv ∧ s209.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_147_eo__24str_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s209
    rcases Store.boolean_value_term h_v287 with ⟨hx_288, hbv_288⟩ | ⟨hx_288, hbv_288⟩ | ⟨hx_288, hbv_288⟩
    · ite_branch hbv_288
      ite_done hinv209 hG with (eo_ite_true_rep _ hx_288 h_v2)
    · ite_branch hbv_288
      step as ⟨e_v288, he_v288⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s209 e_v288 (by rw [he_v288]; exact empty_args) hinv209 h64 as ⟨v288, s210, hinv210, h_v288⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping h_v287 he_v288 e_v288 v287
      store_step with Store.apply_rep s210 v288 v2 _ _ hinv210 h64 h_v288 h_v2 (by ns_tac) (by ns_tac) as ⟨v289, s211, hinv211, h_v289⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping h_v288 v288
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s211 0#u32 (0) (by scalar_tac) hinv211 h64 as ⟨v290, s212, hinv212, h_v290⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v289 dropping
      store_step with Store.apply_rep s212 v289 v290 _ _ hinv212 h64 h_v289 h_v290 (by ns_tac) (by ns_tac) as ⟨v291, s213, hinv213, h_v291⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping h_v289 h_v290 v289 v290
      step as ⟨e_v292, he_v292⟩
      store_step with CtorSpec.eo__2d.construct s213 e_v292 (by rw [he_v292]; exact empty_args) hinv213 h64 as ⟨v292, s214, hinv214, h_v292⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v291 dropping he_v292 e_v292
      step as ⟨e_v293, he_v293⟩
      store_step with CtorSpec.eo_str_2elen.construct s214 e_v293 (by rw [he_v293]; exact empty_args) hinv214 h64 as ⟨v293, s215, hinv215, h_v293⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v291 h_v292 dropping he_v293 e_v293
      store_step with Store.apply_rep s215 v293 v8 _ _ hinv215 h64 h_v293 h_v8 (by ns_tac) (by ns_tac) as ⟨v294, s216, hinv216, h_v294⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v291 h_v292 dropping h_v293 v293
      store_step with Store.apply_rep s216 v292 v294 _ _ hinv216 h64 h_v292 h_v294 (by ns_tac) (by ns_tac) as ⟨v295, s217, hinv217, h_v295⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v291 dropping h_v292 h_v294 v292 v294
      store_step with Store.apply_rep s217 v295 v5 _ _ hinv217 h64 h_v295 h_v5 (by ns_tac) (by ns_tac) as ⟨v296, s218, hinv218, h_v296⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 h_v291 dropping h_v295 v295
      store_step with Store.apply_rep s218 v291 v296 _ _ hinv218 h64 h_v291 h_v296 (by ns_tac) (by ns_tac) as ⟨v297, s219, hinv219, h_v297⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping h_v291 h_v296 v291 v296
      ite_done hinv219 hG with (eo_ite_false_rep _ hx_288 h_v297)
    · ite_branch hbv_288
      ite_stuck hinv209 hG with hx_288)
  store_step with h_ite_v298 as ⟨v298, s210, hinv210, h_v298⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 h_v284 dropping h_ite_v298 h_v287 hinv209 s209 v287
  store_step with Store.apply_mk_rep s210 v284 v298 _ _ hinv210 h64 h_v284 h_v298 as ⟨v299, s211, hinv211, h_v299⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 h_v283 dropping h_v284 h_v298 hinv210 s210 v284 v298
  store_step with Store.apply_mk_rep s211 v283 v299 _ _ hinv211 h64 h_v283 h_v299 as ⟨v300, s212, hinv212, h_v300⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 h_v280 dropping h_v283 h_v299 hinv211 s211 v283 v299
  store_step with Store.apply_mk_rep s212 v280 v300 _ _ hinv212 h64 h_v280 h_v300 as ⟨v301, s213, hinv213, h_v301⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 h_v279 dropping h_v280 h_v300 hinv212 s212 v280 v300
  store_step with Store.apply_mk_rep s213 v279 v301 _ _ hinv213 h64 h_v279 h_v301 as ⟨v302, s214, hinv214, h_v302⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 h_v278 dropping h_v279 h_v301 hinv213 s213 v279 v301
  store_step with Store.apply_mk_rep s214 v278 v302 _ _ hinv214 h64 h_v278 h_v302 as ⟨v303, s215, hinv215, h_v303⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v260 dropping h_v278 h_v302 hinv214 s214 v278 v302
  store_step with Store.apply_mk_rep s215 v260 v303 _ _ hinv215 h64 h_v260 h_v303 as ⟨v304, s216, hinv216, h_v304⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 dropping h_v260 h_v303 hinv215 s215 v260 v303
  store_step with Store.literal_boolean_spec s216 true hinv216 h64 as ⟨v305, s217, hinv217, h_v305⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 h_v304 dropping hinv216 s216
  store_step with Store.apply_mk_rep s217 v304 v305 _ _ hinv217 h64 h_v304 h_v305 as ⟨v306, s218, hinv218, h_v306⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 h_v259 dropping h_v304 h_v305 hinv217 s217 v304 v305
  store_step with Store.apply_mk_rep s218 v259 v306 _ _ hinv218 h64 h_v259 h_v306 as ⟨v307, s219, hinv219, h_v307⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 h_v245 dropping h_v259 h_v306 hinv218 s218 v259 v306
  store_step with Store.apply_mk_rep s219 v245 v307 _ _ hinv219 h64 h_v245 h_v307 as ⟨v308, s220, hinv220, h_v308⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 h_v135 dropping h_v245 h_v307 hinv219 s219 v245 v307
  store_step with Store.apply_mk_rep s220 v135 v308 _ _ hinv220 h64 h_v135 h_v308 as ⟨v309, s221, hinv221, h_v309⟩ growing hG carrying h_v2 h_v5 h_v8 h_v27 dropping h_v135 h_v308 hinv220 s220 v135 v308
  store_step with Store.apply_mk_rep s221 v27 v309 _ _ hinv221 h64 h_v27 h_v309 as ⟨v310, s222, hinv222, h_v310⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v27 h_v309 hinv221 s221 v27 v309
  step as ⟨e_v311, he_v311⟩
  store_step with CtorSpec.eo__3d.construct s222 e_v311 (by rw [he_v311]; exact empty_args) hinv222 h64 as ⟨v311, s223, hinv223, h_v311⟩ growing hG carrying h_v2 h_v5 h_v8 h_v310 dropping he_v311 hinv222 e_v311 s222
  step as ⟨e_v312, he_v312⟩
  store_step with CtorSpec.eo__40purify.construct s223 e_v312 (by rw [he_v312]; exact empty_args) hinv223 h64 as ⟨v312, s224, hinv224, h_v312⟩ growing hG carrying h_v2 h_v5 h_v8 h_v310 h_v311 dropping he_v312 hinv223 e_v312 s223
  step as ⟨e_v313, he_v313⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s224 e_v313 (by rw [he_v313]; exact empty_args) hinv224 h64 as ⟨v313, s225, hinv225, h_v313⟩ growing hG carrying h_v2 h_v5 h_v8 h_v310 h_v311 h_v312 dropping he_v313 hinv224 e_v313 s224
  store_step with Store.apply_rep s225 v313 v8 _ _ hinv225 h64 h_v313 h_v8 (by ns_tac) (by ns_tac) as ⟨v314, s226, hinv226, h_v314⟩ growing hG carrying h_v2 h_v5 h_v8 h_v310 h_v311 h_v312 dropping h_v313 hinv225 s225 v313
  store_step with Store.apply_rep s226 v314 v5 _ _ hinv226 h64 h_v314 h_v5 (by ns_tac) (by ns_tac) as ⟨v315, s227, hinv227, h_v315⟩ growing hG carrying h_v2 h_v8 h_v310 h_v311 h_v312 dropping h_v314 h_v5 hinv226 s226 v314 v5
  store_step with Store.apply_rep s227 v315 v2 _ _ hinv227 h64 h_v315 h_v2 (by ns_tac) (by ns_tac) as ⟨v316, s228, hinv228, h_v316⟩ growing hG carrying h_v8 h_v310 h_v311 h_v312 dropping h_v2 h_v315 hinv227 s227 v2 v315
  store_step with Store.apply_rep s228 v312 v316 _ _ hinv228 h64 h_v312 h_v316 (by ns_tac) (by ns_tac) as ⟨v317, s229, hinv229, h_v317⟩ growing hG carrying h_v8 h_v310 h_v311 dropping h_v312 h_v316 hinv228 s228 v312 v316
  store_step with Store.apply_rep s229 v311 v317 _ _ hinv229 h64 h_v311 h_v317 (by ns_tac) (by ns_tac) as ⟨v318, s230, hinv230, h_v318⟩ growing hG carrying h_v8 h_v310 dropping h_v311 h_v317 hinv229 s229 v311 v317
  store_step with Store.apply_rep s230 v318 v8 _ _ hinv230 h64 h_v318 h_v8 (by ns_tac) (by ns_tac) as ⟨v319, s231, hinv231, h_v319⟩ growing hG carrying h_v310 dropping h_v318 h_v8 hinv230 s230 v318 v8
  store_step with Store.apply_mk_rep s231 v310 v319 _ _ hinv231 h64 h_v310 h_v319 as ⟨v320, s232, hinv232, h_v320⟩ growing hG carrying dropping h_v310 h_v319 hinv231 s231 v310 v319
  case_done hinv232 hG with h_v320 in EoCases.__str_reduction_pred.case_7 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

end pathos_compiled_checker
