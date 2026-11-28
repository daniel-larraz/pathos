module
public import $PROOFS$.Head
public import $PROOFS$.Part41
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

set_option maxHeartbeats 9480000 in
theorem case_8_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_8_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_8
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_8
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  store_step with Store.apply_rep s3 v11 v5 _ _ hinv3 h64 h_v11 h_v5 (by ns_tac) (by ns_tac) as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 hinv3 s3 v11
  store_step with ih.eo__24eo_5ftypeof s4 v8 _ hinv4 h64 (hG.rem hrem) h_v8 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v12 dropping hinv4 s4
  store_step with ih.eo__24seq_5fempty s5 v13 _ hinv5 h64 (hG.rem hrem) h_v13 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v12 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_mk_rep s6 v12 v14 _ _ hinv6 h64 h_v12 h_v14 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v12 h_v14 hinv6 s6 v12 v14
  store_step with Store.apply_mk_rep s7 v10 v15 _ _ hinv7 h64 h_v10 h_v15 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v15 hinv7 s7 v10 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 dropping he_v17 hinv8 e_v17 s8
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__40purify.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 dropping he_v18 hinv9 e_v18 s9
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s10 e_v19 (by rw [he_v19]; exact empty_args) hinv10 h64 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping he_v19 hinv10 e_v19 s10
  store_step with Store.apply_rep s11 v19 v8 _ _ hinv11 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping h_v19 hinv11 s11 v19
  store_step with Store.apply_rep s12 v20 v5 _ _ hinv12 h64 h_v20 h_v5 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping h_v20 hinv12 s12 v20
  store_step with Store.apply_rep s13 v21 v2 _ _ hinv13 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 h_v18 dropping h_v21 hinv13 s13 v21
  store_step with Store.apply_rep s14 v18 v22 _ _ hinv14 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 h_v17 dropping h_v18 h_v22 hinv14 s14 v18 v22
  store_step with Store.apply_rep s15 v17 v23 _ _ hinv15 h64 h_v17 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 dropping h_v17 h_v23 hinv15 s15 v17 v23
  store_step with Store.apply_rep s16 v24 v8 _ _ hinv16 h64 h_v24 h_v8 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v16 dropping h_v24 hinv16 s16 v24
  store_step with Store.apply_mk_rep s17 v16 v25 _ _ hinv17 h64 h_v16 h_v25 as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v16 h_v25 hinv17 s17 v16 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_and.construct s18 e_v27 (by rw [he_v27]; exact empty_args) hinv18 h64 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 dropping he_v27 hinv18 e_v27 s18
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__3e_3d.construct s19 e_v28 (by rw [he_v28]; exact empty_args) hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 dropping he_v28 hinv19 e_v28 s19
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s20 e_v29 (by rw [he_v29]; exact empty_args) hinv20 h64 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping he_v29 hinv20 e_v29 s20
  store_step with Store.apply_rep s21 v29 v8 _ _ hinv21 h64 h_v29 h_v8 (by ns_tac) (by ns_tac) as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping h_v29 hinv21 s21 v29
  store_step with Store.apply_rep s22 v30 v5 _ _ hinv22 h64 h_v30 h_v5 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping h_v30 hinv22 s22 v30
  store_step with Store.apply_rep s23 v28 v31 _ _ hinv23 h64 h_v28 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 dropping h_v28 h_v31 hinv23 s23 v28 v31
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s24 0#u32 (0) (by scalar_tac) hinv24 h64 as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v32 dropping hinv24 s24
  store_step with Store.apply_rep s25 v32 v33 _ _ hinv25 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 dropping h_v32 h_v33 hinv25 s25 v32 v33
  store_step with Store.apply_rep s26 v27 v34 _ _ hinv26 h64 h_v27 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 dropping h_v27 h_v34 hinv26 s26 v27 v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_and.construct s27 e_v36 (by rw [he_v36]; exact empty_args) hinv27 h64 as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 dropping he_v36 hinv27 e_v36 s27
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s28 e_v37 (by rw [he_v37]; exact empty_args) hinv28 h64 as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 dropping he_v37 hinv28 e_v37 s28
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__40purify.construct s29 e_v38 (by rw [he_v38]; exact empty_args) hinv29 h64 as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v37 dropping he_v38 hinv29 e_v38 s29
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s30 e_v39 (by rw [he_v39]; exact empty_args) hinv30 h64 as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v37 h_v38 dropping he_v39 hinv30 e_v39 s30
  store_step with Store.apply_rep s31 v39 v8 _ _ hinv31 h64 h_v39 h_v8 (by ns_tac) (by ns_tac) as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v37 h_v38 dropping h_v39 hinv31 s31 v39
  store_step with Store.apply_rep s32 v40 v5 _ _ hinv32 h64 h_v40 h_v5 (by ns_tac) (by ns_tac) as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v37 h_v38 dropping h_v40 hinv32 s32 v40
  store_step with Store.apply_rep s33 v41 v2 _ _ hinv33 h64 h_v41 h_v2 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v37 h_v38 dropping h_v41 hinv33 s33 v41
  store_step with Store.apply_rep s34 v38 v42 _ _ hinv34 h64 h_v38 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v37 dropping h_v38 h_v42 hinv34 s34 v38 v42
  store_step with Store.apply_rep s35 v37 v43 _ _ hinv35 h64 h_v37 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 dropping h_v37 h_v43 hinv35 s35 v37 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct s36 e_v45 (by rw [he_v45]; exact empty_args) hinv36 h64 as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v44 dropping he_v45 hinv36 e_v45 s36
  store_step with Store.apply_rep s37 v45 v8 _ _ hinv37 h64 h_v45 h_v8 (by ns_tac) (by ns_tac) as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v44 dropping h_v45 hinv37 s37 v45
  store_step with Store.apply_rep s38 v46 v5 _ _ hinv38 h64 h_v46 h_v5 (by ns_tac) (by ns_tac) as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v44 dropping h_v46 hinv38 s38 v46
  store_step with Store.apply_rep s39 v47 v2 _ _ hinv39 h64 h_v47 h_v2 (by ns_tac) (by ns_tac) as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v44 dropping h_v47 hinv39 s39 v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s40 0#u32 (0) (by scalar_tac) hinv40 h64 as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v44 h_v48 dropping hinv40 s40
  store_step with Store.apply_rep s41 v48 v49 _ _ hinv41 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 h_v44 dropping h_v48 h_v49 hinv41 s41 v48 v49
  store_step with Store.apply_rep s42 v44 v50 _ _ hinv42 h64 h_v44 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v36 dropping h_v44 h_v50 hinv42 s42 v44 v50
  store_step with Store.apply_rep s43 v36 v51 _ _ hinv43 h64 h_v36 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 dropping h_v36 h_v51 hinv43 s43 v36 v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_and.construct s44 e_v53 (by rw [he_v53]; exact empty_args) hinv44 h64 as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 dropping he_v53 hinv44 e_v53 s44
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s45 e_v54 (by rw [he_v54]; exact empty_args) hinv45 h64 as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 dropping he_v54 hinv45 e_v54 s45
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct s46 e_v55 (by rw [he_v55]; exact empty_args) hinv46 h64 as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 dropping he_v55 hinv46 e_v55 s46
  store_step with Store.apply_rep s47 v55 v8 _ _ hinv47 h64 h_v55 h_v8 (by ns_tac) (by ns_tac) as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 dropping h_v55 hinv47 s47 v55
  store_step with Store.apply_rep s48 v56 v5 _ _ hinv48 h64 h_v56 h_v5 (by ns_tac) (by ns_tac) as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 dropping h_v56 hinv48 s48 v56
  store_step with Store.apply_rep s49 v57 v2 _ _ hinv49 h64 h_v57 h_v2 (by ns_tac) (by ns_tac) as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 dropping h_v57 hinv49 s49 v57
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s50 e_v59 (by rw [he_v59]; exact empty_args) hinv50 h64 as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 h_v58 dropping he_v59 hinv50 e_v59 s50
  store_step with Store.apply_rep s51 v59 v8 _ _ hinv51 h64 h_v59 h_v8 (by ns_tac) (by ns_tac) as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 h_v58 dropping h_v59 hinv51 s51 v59
  store_step with Store.apply_rep s52 v60 v5 _ _ hinv52 h64 h_v60 h_v5 (by ns_tac) (by ns_tac) as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 h_v58 dropping h_v60 hinv52 s52 v60
  store_step with Store.apply_rep s53 v58 v61 _ _ hinv53 h64 h_v58 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v54 dropping h_v58 h_v61 hinv53 s53 v58 v61
  store_step with Store.apply_rep s54 v54 v62 _ _ hinv54 h64 h_v54 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 dropping h_v54 h_v62 hinv54 s54 v54 v62
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s55 e_v64 (by rw [he_v64]; exact empty_args) hinv55 h64 as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 dropping he_v64 hinv55 e_v64 s55
  store_step with Store.apply_rep s56 v64 v8 _ _ hinv56 h64 h_v64 h_v8 (by ns_tac) (by ns_tac) as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 dropping h_v64 hinv56 s56 v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s57 e_v66 (by rw [he_v66]; exact empty_args) hinv57 h64 as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 dropping he_v66 hinv57 e_v66 s57
  store_step with Store.apply_rep s58 v66 v8 _ _ hinv58 h64 h_v66 h_v8 (by ns_tac) (by ns_tac) as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 dropping h_v66 hinv58 s58 v66
  store_step with Store.apply_rep s59 v67 v5 _ _ hinv59 h64 h_v67 h_v5 (by ns_tac) (by ns_tac) as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 dropping h_v67 hinv59 s59 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s60 e_v69 (by rw [he_v69]; exact empty_args) hinv60 h64 as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 h_v68 dropping he_v69 hinv60 e_v69 s60
  store_step with Store.apply_rep s61 v69 v8 _ _ hinv61 h64 h_v69 h_v8 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 h_v68 dropping h_v69 hinv61 s61 v69
  store_step with Store.apply_rep s62 v70 v5 _ _ hinv62 h64 h_v70 h_v5 (by ns_tac) (by ns_tac) as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 h_v68 dropping h_v70 hinv62 s62 v70
  store_step with Store.apply_rep s63 v68 v71 _ _ hinv63 h64 h_v68 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v65 dropping h_v68 h_v71 hinv63 s63 v68 v71
  store_step with Store.apply_rep s64 v65 v72 _ _ hinv64 h64 h_v65 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 dropping h_v65 h_v72 hinv64 s64 v65 v72
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_str_2elen.construct s65 e_v74 (by rw [he_v74]; exact empty_args) hinv65 h64 as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v73 dropping he_v74 hinv65 e_v74 s65
  store_step with Store.apply_rep s66 v74 v8 _ _ hinv66 h64 h_v74 h_v8 (by ns_tac) (by ns_tac) as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 h_v73 dropping h_v74 hinv66 s66 v74
  store_step with Store.apply_rep s67 v73 v75 _ _ hinv67 h64 h_v73 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 h_v63 dropping h_v73 h_v75 hinv67 s67 v73 v75
  store_step with Store.apply_rep s68 v63 v76 _ _ hinv68 h64 h_v63 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v53 dropping h_v63 h_v76 hinv68 s68 v63 v76
  store_step with Store.apply_rep s69 v53 v77 _ _ hinv69 h64 h_v53 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 dropping h_v53 h_v77 hinv69 s69 v53 v77
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_and.construct s70 e_v79 (by rw [he_v79]; exact empty_args) hinv70 h64 as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 dropping he_v79 hinv70 e_v79 s70
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo__3d.construct s71 e_v80 (by rw [he_v80]; exact empty_args) hinv71 h64 as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 dropping he_v80 hinv71 e_v80 s71
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s72 e_v81 (by rw [he_v81]; exact empty_args) hinv72 h64 as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 h_v80 dropping he_v81 hinv72 e_v81 s72
  store_step with Store.apply_rep s73 v81 v8 _ _ hinv73 h64 h_v81 h_v8 (by ns_tac) (by ns_tac) as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 h_v80 dropping h_v81 hinv73 s73 v81
  store_step with Store.apply_rep s74 v82 v5 _ _ hinv74 h64 h_v82 h_v5 (by ns_tac) (by ns_tac) as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 h_v80 dropping h_v82 hinv74 s74 v82
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s75 0#u32 (0) (by scalar_tac) hinv75 h64 as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 h_v80 h_v83 dropping hinv75 s75
  store_step with Store.apply_rep s76 v83 v84 _ _ hinv76 h64 h_v83 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 h_v80 dropping h_v83 h_v84 hinv76 s76 v83 v84
  store_step with Store.apply_rep s77 v80 v85 _ _ hinv77 h64 h_v80 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 dropping h_v80 h_v85 hinv77 s77 v80 v85
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s78 0#u32 (0) (by scalar_tac) hinv78 h64 as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 h_v86 dropping hinv78 s78
  store_step with Store.apply_rep s79 v86 v87 _ _ hinv79 h64 h_v86 h_v87 (by ns_tac) (by ns_tac) as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v79 dropping h_v86 h_v87 hinv79 s79 v86 v87
  store_step with Store.apply_rep s80 v79 v88 _ _ hinv80 h64 h_v79 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 dropping h_v79 h_v88 hinv80 s80 v79 v88
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_and.construct s81 e_v90 (by rw [he_v90]; exact empty_args) hinv81 h64 as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 dropping he_v90 hinv81 e_v90 s81
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__3d.construct s82 e_v91 (by rw [he_v91]; exact empty_args) hinv82 h64 as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 dropping he_v91 hinv82 e_v91 s82
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s83 e_v92 (by rw [he_v92]; exact empty_args) hinv83 h64 as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 dropping he_v92 hinv83 e_v92 s83
  store_step with Store.apply_rep s84 v92 v8 _ _ hinv84 h64 h_v92 h_v8 (by ns_tac) (by ns_tac) as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 dropping h_v92 hinv84 s84 v92
  store_step with Store.apply_rep s85 v93 v5 _ _ hinv85 h64 h_v93 h_v5 (by ns_tac) (by ns_tac) as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 dropping h_v93 hinv85 s85 v93
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s86 e_v95 (by rw [he_v95]; exact empty_args) hinv86 h64 as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 dropping he_v95 hinv86 e_v95 s86
  store_step with Store.apply_rep s87 v95 v8 _ _ hinv87 h64 h_v95 h_v8 (by ns_tac) (by ns_tac) as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 dropping h_v95 hinv87 s87 v95
  store_step with Store.apply_rep s88 v96 v5 _ _ hinv88 h64 h_v96 h_v5 (by ns_tac) (by ns_tac) as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 dropping h_v96 hinv88 s88 v96
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s89 e_v98 (by rw [he_v98]; exact empty_args) hinv89 h64 as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 h_v97 dropping he_v98 hinv89 e_v98 s89
  store_step with Store.apply_rep s90 v98 v8 _ _ hinv90 h64 h_v98 h_v8 (by ns_tac) (by ns_tac) as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 h_v97 dropping h_v98 hinv90 s90 v98
  store_step with Store.apply_rep s91 v99 v5 _ _ hinv91 h64 h_v99 h_v5 (by ns_tac) (by ns_tac) as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 h_v97 dropping h_v99 hinv91 s91 v99
  store_step with Store.apply_rep s92 v97 v100 _ _ hinv92 h64 h_v97 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 h_v94 dropping h_v100 h_v97 hinv92 s92 v100 v97
  store_step with Store.apply_rep s93 v94 v101 _ _ hinv93 h64 h_v94 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v91 dropping h_v101 h_v94 hinv93 s93 v101 v94
  store_step with Store.apply_rep s94 v91 v102 _ _ hinv94 h64 h_v91 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 dropping h_v102 h_v91 hinv94 s94 v102 v91
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s95 1#u32 (-1) (by scalar_tac) hinv95 h64 as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 h_v103 dropping hinv95 s95
  store_step with Store.apply_rep s96 v103 v104 _ _ hinv96 h64 h_v103 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v90 dropping h_v103 h_v104 hinv96 s96 v103 v104
  store_step with Store.apply_rep s97 v90 v105 _ _ hinv97 h64 h_v90 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 dropping h_v105 h_v90 hinv97 s97 v105 v90
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_and.construct s98 e_v107 (by rw [he_v107]; exact empty_args) hinv98 h64 as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 dropping he_v107 hinv98 e_v107 s98
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_forall.construct s99 e_v108 (by rw [he_v108]; exact empty_args) hinv99 h64 as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 dropping he_v108 hinv99 e_v108 s99
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s100 e_v109 (by rw [he_v109]; exact empty_args) hinv100 h64 as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 dropping he_v109 hinv100 e_v109 s100
  step as ⟨e_v110, he_v110⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s101 _ _ rfl hinv101 h64 as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 h_v109 dropping hinv101 s101
  replace h_v110 := Represents.rep_of_eq h_v110 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v110]; decide)
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo_Int.construct s102 e_v111 (by rw [he_v111]; exact empty_args) hinv102 h64 as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 h_v109 h_v110 dropping he_v110 he_v111 hinv102 e_v110 e_v111 s102
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s103 e_v112 (by rw [he_v112]; rfl) h_v110 h_v111 hinv103 h64 as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 h_v109 dropping h_v110 h_v111 he_v112 hinv103 e_v112 s103 v110 v111
  store_step with Store.apply_rep s104 v109 v112 _ _ hinv104 h64 h_v109 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 dropping h_v109 h_v112 hinv104 s104 v109 v112
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s105 e_v114 (by rw [he_v114]; exact empty_args) hinv105 h64 as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 h_v113 dropping he_v114 hinv105 e_v114 s105
  store_step with Store.apply_rep s106 v113 v114 _ _ hinv106 h64 h_v113 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v108 dropping h_v113 h_v114 hinv106 s106 v113 v114
  store_step with Store.apply_rep s107 v108 v115 _ _ hinv107 h64 h_v108 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 dropping h_v108 h_v115 hinv107 s107 v108 v115
  step as ⟨e_v117, he_v117⟩
  store_step with CtorSpec.eo_or.construct s108 e_v117 (by rw [he_v117]; exact empty_args) hinv108 h64 as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 dropping he_v117 hinv108 e_v117 s108
  step as ⟨e_v118, he_v118⟩
  store_step with CtorSpec.eo_not.construct s109 e_v118 (by rw [he_v118]; exact empty_args) hinv109 h64 as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 dropping he_v118 hinv109 e_v118 s109
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo__3e_3d.construct s110 e_v119 (by rw [he_v119]; exact empty_args) hinv110 h64 as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 dropping he_v119 hinv110 e_v119 s110
  step as ⟨e_v120, he_v120⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s111 _ _ rfl hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 h_v119 dropping hinv111 s111
  replace h_v120 := Represents.rep_of_eq h_v120 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v120]; decide)
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_Int.construct s112 e_v121 (by rw [he_v121]; exact empty_args) hinv112 h64 as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 h_v119 h_v120 dropping he_v120 he_v121 hinv112 e_v120 e_v121 s112
  step as ⟨e_v122, he_v122⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s113 e_v122 (by rw [he_v122]; rfl) h_v120 h_v121 hinv113 h64 as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 h_v119 dropping h_v120 h_v121 he_v122 hinv113 e_v122 s113 v120 v121
  store_step with Store.apply_rep s114 v119 v122 _ _ hinv114 h64 h_v119 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 dropping h_v119 h_v122 hinv114 s114 v119 v122
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s115 0#u32 (0) (by scalar_tac) hinv115 h64 as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 h_v123 dropping hinv115 s115
  store_step with Store.apply_rep s116 v123 v124 _ _ hinv116 h64 h_v123 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 h_v118 dropping h_v123 h_v124 hinv116 s116 v123 v124
  store_step with Store.apply_rep s117 v118 v125 _ _ hinv117 h64 h_v118 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v117 dropping h_v118 h_v125 hinv117 s117 v118 v125
  store_step with Store.apply_rep s118 v117 v126 _ _ hinv118 h64 h_v117 h_v126 (by ns_tac) (by ns_tac) as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 dropping h_v117 h_v126 hinv118 s118 v117 v126
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo_or.construct s119 e_v128 (by rw [he_v128]; exact empty_args) hinv119 h64 as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 dropping he_v128 hinv119 e_v128 s119
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo_not.construct s120 e_v129 (by rw [he_v129]; exact empty_args) hinv120 h64 as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 dropping he_v129 hinv120 e_v129 s120
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo__3c.construct s121 e_v130 (by rw [he_v130]; exact empty_args) hinv121 h64 as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 dropping he_v130 hinv121 e_v130 s121
  step as ⟨e_v131, he_v131⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s122 _ _ rfl hinv122 h64 as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 h_v130 dropping hinv122 s122
  replace h_v131 := Represents.rep_of_eq h_v131 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v131]; decide)
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo_Int.construct s123 e_v132 (by rw [he_v132]; exact empty_args) hinv123 h64 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 h_v130 h_v131 dropping he_v131 he_v132 hinv123 e_v131 e_v132 s123
  step as ⟨e_v133, he_v133⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s124 e_v133 (by rw [he_v133]; rfl) h_v131 h_v132 hinv124 h64 as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 h_v130 dropping h_v131 h_v132 he_v133 hinv124 e_v133 s124 v131 v132
  store_step with Store.apply_rep s125 v130 v133 _ _ hinv125 h64 h_v130 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 dropping h_v130 h_v133 hinv125 s125 v130 v133
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur.construct s126 e_v135 (by rw [he_v135]; exact empty_args) hinv126 h64 as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 h_v134 dropping he_v135 hinv126 e_v135 s126
  store_step with Store.apply_rep s127 v135 v8 _ _ hinv127 h64 h_v135 h_v8 (by ns_tac) (by ns_tac) as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 h_v134 dropping h_v135 hinv127 s127 v135
  store_step with Store.apply_rep s128 v136 v5 _ _ hinv128 h64 h_v136 h_v5 (by ns_tac) (by ns_tac) as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 h_v134 dropping h_v136 hinv128 s128 v136
  store_step with Store.apply_rep s129 v134 v137 _ _ hinv129 h64 h_v134 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 h_v129 dropping h_v134 h_v137 hinv129 s129 v134 v137
  store_step with Store.apply_rep s130 v129 v138 _ _ hinv130 h64 h_v129 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v128 dropping h_v129 h_v138 hinv130 s130 v129 v138
  store_step with Store.apply_rep s131 v128 v139 _ _ hinv131 h64 h_v128 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 dropping h_v128 h_v139 hinv131 s131 v128 v139
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo_or.construct s132 e_v141 (by rw [he_v141]; exact empty_args) hinv132 h64 as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 dropping he_v141 hinv132 e_v141 s132
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo_and.construct s133 e_v142 (by rw [he_v142]; exact empty_args) hinv133 h64 as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 dropping he_v142 hinv133 e_v142 s133
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_not.construct s134 e_v143 (by rw [he_v143]; exact empty_args) hinv134 h64 as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 dropping he_v143 hinv134 e_v143 s134
  step as ⟨e_v144, he_v144⟩
  store_step with CtorSpec.eo__3d.construct s135 e_v144 (by rw [he_v144]; exact empty_args) hinv135 h64 as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 dropping he_v144 hinv135 e_v144 s135
  step as ⟨e_v145, he_v145⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s136 e_v145 (by rw [he_v145]; exact empty_args) hinv136 h64 as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 dropping he_v145 hinv136 e_v145 s136
  store_step with Store.apply_rep s137 v145 v8 _ _ hinv137 h64 h_v145 h_v8 (by ns_tac) (by ns_tac) as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 dropping h_v145 hinv137 s137 v145
  store_step with Store.apply_rep s138 v146 v5 _ _ hinv138 h64 h_v146 h_v5 (by ns_tac) (by ns_tac) as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 dropping h_v146 hinv138 s138 v146
  step as ⟨e_v148, he_v148⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s139 e_v148 (by rw [he_v148]; exact empty_args) hinv139 h64 as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 dropping he_v148 hinv139 e_v148 s139
  store_step with Store.apply_rep s140 v148 v8 _ _ hinv140 h64 h_v148 h_v8 (by ns_tac) (by ns_tac) as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 dropping h_v148 hinv140 s140 v148
  store_step with Store.apply_rep s141 v149 v5 _ _ hinv141 h64 h_v149 h_v5 (by ns_tac) (by ns_tac) as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 dropping h_v149 hinv141 s141 v149
  step as ⟨e_v151, he_v151⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s142 _ _ rfl hinv142 h64 as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 h_v150 dropping hinv142 s142
  replace h_v151 := Represents.rep_of_eq h_v151 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v151]; decide)
  step as ⟨e_v152, he_v152⟩
  store_step with CtorSpec.eo_Int.construct s143 e_v152 (by rw [he_v152]; exact empty_args) hinv143 h64 as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 h_v150 h_v151 dropping he_v151 he_v152 hinv143 e_v151 e_v152 s143
  step as ⟨e_v153, he_v153⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s144 e_v153 (by rw [he_v153]; rfl) h_v151 h_v152 hinv144 h64 as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 h_v150 dropping h_v151 h_v152 he_v153 hinv144 e_v153 s144 v151 v152
  store_step with Store.apply_rep s145 v150 v153 _ _ hinv145 h64 h_v150 h_v153 (by ns_tac) (by ns_tac) as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 h_v147 dropping h_v150 h_v153 hinv145 s145 v150 v153
  store_step with Store.apply_rep s146 v147 v154 _ _ hinv146 h64 h_v147 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v144 dropping h_v147 h_v154 hinv146 s146 v147 v154
  store_step with Store.apply_rep s147 v144 v155 _ _ hinv147 h64 h_v144 h_v155 (by ns_tac) (by ns_tac) as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 dropping h_v144 h_v155 hinv147 s147 v144 v155
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s148 1#u32 (-1) (by scalar_tac) hinv148 h64 as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 h_v156 dropping hinv148 s148
  store_step with Store.apply_rep s149 v156 v157 _ _ hinv149 h64 h_v156 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 h_v143 dropping h_v156 h_v157 hinv149 s149 v156 v157
  store_step with Store.apply_rep s150 v143 v158 _ _ hinv150 h64 h_v143 h_v158 (by ns_tac) (by ns_tac) as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v142 dropping h_v143 h_v158 hinv150 s150 v143 v158
  store_step with Store.apply_rep s151 v142 v159 _ _ hinv151 h64 h_v142 h_v159 (by ns_tac) (by ns_tac) as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 dropping h_v142 h_v159 hinv151 s151 v142 v159
  step as ⟨e_v161, he_v161⟩
  store_step with CtorSpec.eo_and.construct s152 e_v161 (by rw [he_v161]; exact empty_args) hinv152 h64 as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 dropping he_v161 hinv152 e_v161 s152
  step as ⟨e_v162, he_v162⟩
  store_step with CtorSpec.eo__3d.construct s153 e_v162 (by rw [he_v162]; exact empty_args) hinv153 h64 as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 dropping he_v162 hinv153 e_v162 s153
  step as ⟨e_v163, he_v163⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct s154 e_v163 (by rw [he_v163]; exact empty_args) hinv154 h64 as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 dropping he_v163 hinv154 e_v163 s154
  store_step with Store.apply_rep s155 v163 v8 _ _ hinv155 h64 h_v163 h_v8 (by ns_tac) (by ns_tac) as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 dropping h_v163 hinv155 s155 v163
  store_step with Store.apply_rep s156 v164 v5 _ _ hinv156 h64 h_v164 h_v5 (by ns_tac) (by ns_tac) as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 dropping h_v164 hinv156 s156 v164
  store_step with Store.apply_rep s157 v165 v2 _ _ hinv157 h64 h_v165 h_v2 (by ns_tac) (by ns_tac) as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 dropping h_v165 hinv157 s157 v165
  step as ⟨e_v167, he_v167⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s158 _ _ rfl hinv158 h64 as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 h_v166 dropping hinv158 s158
  replace h_v167 := Represents.rep_of_eq h_v167 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v167]; decide)
  step as ⟨e_v168, he_v168⟩
  store_step with CtorSpec.eo_Int.construct s159 e_v168 (by rw [he_v168]; exact empty_args) hinv159 h64 as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 h_v166 h_v167 dropping he_v167 he_v168 hinv159 e_v167 e_v168 s159
  step as ⟨e_v169, he_v169⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s160 e_v169 (by rw [he_v169]; rfl) h_v167 h_v168 hinv160 h64 as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 h_v166 dropping h_v167 h_v168 he_v169 hinv160 e_v169 s160 v167 v168
  store_step with Store.apply_rep s161 v166 v169 _ _ hinv161 h64 h_v166 h_v169 (by ns_tac) (by ns_tac) as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v162 dropping h_v166 h_v169 hinv161 s161 v166 v169
  store_step with Store.apply_rep s162 v162 v170 _ _ hinv162 h64 h_v162 h_v170 (by ns_tac) (by ns_tac) as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 dropping h_v162 h_v170 hinv162 s162 v162 v170
  step as ⟨e_v172, he_v172⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s163 e_v172 (by rw [he_v172]; exact empty_args) hinv163 h64 as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 dropping he_v172 hinv163 e_v172 s163
  step as ⟨e_v173, he_v173⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s164 e_v173 (by rw [he_v173]; exact empty_args) hinv164 h64 as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 dropping he_v173 hinv164 e_v173 s164
  store_step with Store.apply_rep s165 v173 v8 _ _ hinv165 h64 h_v173 h_v8 (by ns_tac) (by ns_tac) as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 dropping h_v173 hinv165 s165 v173
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s166 e_v175 (by rw [he_v175]; exact empty_args) hinv166 h64 as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 dropping he_v175 hinv166 e_v175 s166
  store_step with Store.apply_rep s167 v175 v8 _ _ hinv167 h64 h_v175 h_v8 (by ns_tac) (by ns_tac) as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 dropping h_v175 hinv167 s167 v175
  store_step with Store.apply_rep s168 v176 v5 _ _ hinv168 h64 h_v176 h_v5 (by ns_tac) (by ns_tac) as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 dropping h_v176 hinv168 s168 v176
  step as ⟨e_v178, he_v178⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s169 _ _ rfl hinv169 h64 as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 h_v177 dropping hinv169 s169
  replace h_v178 := Represents.rep_of_eq h_v178 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v178]; decide)
  step as ⟨e_v179, he_v179⟩
  store_step with CtorSpec.eo_Int.construct s170 e_v179 (by rw [he_v179]; exact empty_args) hinv170 h64 as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 h_v177 h_v178 dropping he_v178 he_v179 hinv170 e_v178 e_v179 s170
  step as ⟨e_v180, he_v180⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s171 e_v180 (by rw [he_v180]; rfl) h_v178 h_v179 hinv171 h64 as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 h_v177 dropping h_v178 h_v179 he_v180 hinv171 e_v180 s171 v178 v179
  store_step with Store.apply_rep s172 v177 v180 _ _ hinv172 h64 h_v177 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v174 dropping h_v177 h_v180 hinv172 s172 v177 v180
  store_step with Store.apply_rep s173 v174 v181 _ _ hinv173 h64 h_v174 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 dropping h_v174 h_v181 hinv173 s173 v174 v181
  step as ⟨e_v183, he_v183⟩
  store_step with CtorSpec.eo__2d.construct s174 e_v183 (by rw [he_v183]; exact empty_args) hinv174 h64 as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 dropping he_v183 hinv174 e_v183 s174
  step as ⟨e_v184, he_v184⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s175 e_v184 (by rw [he_v184]; exact empty_args) hinv175 h64 as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 dropping he_v184 hinv175 e_v184 s175
  store_step with Store.apply_rep s176 v184 v8 _ _ hinv176 h64 h_v184 h_v8 (by ns_tac) (by ns_tac) as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 dropping h_v184 hinv176 s176 v184
  store_step with Store.apply_rep s177 v185 v5 _ _ hinv177 h64 h_v185 h_v5 (by ns_tac) (by ns_tac) as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 dropping h_v185 hinv177 s177 v185
  step as ⟨e_v187, he_v187⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s178 e_v187 (by rw [he_v187]; exact empty_args) hinv178 h64 as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 dropping he_v187 hinv178 e_v187 s178
  store_step with Store.apply_rep s179 v187 v8 _ _ hinv179 h64 h_v187 h_v8 (by ns_tac) (by ns_tac) as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 dropping h_v187 hinv179 s179 v187
  store_step with Store.apply_rep s180 v188 v5 _ _ hinv180 h64 h_v188 h_v5 (by ns_tac) (by ns_tac) as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 dropping h_v188 hinv180 s180 v188
  step as ⟨e_v190, he_v190⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s181 _ _ rfl hinv181 h64 as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 h_v189 dropping hinv181 s181
  replace h_v190 := Represents.rep_of_eq h_v190 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v190]; decide)
  step as ⟨e_v191, he_v191⟩
  store_step with CtorSpec.eo_Int.construct s182 e_v191 (by rw [he_v191]; exact empty_args) hinv182 h64 as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 h_v189 h_v190 dropping he_v190 he_v191 hinv182 e_v190 e_v191 s182
  step as ⟨e_v192, he_v192⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s183 e_v192 (by rw [he_v192]; rfl) h_v190 h_v191 hinv183 h64 as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 h_v189 dropping h_v190 h_v191 he_v192 hinv183 e_v192 s183 v190 v191
  store_step with Store.apply_rep s184 v189 v192 _ _ hinv184 h64 h_v189 h_v192 (by ns_tac) (by ns_tac) as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 h_v186 dropping h_v189 h_v192 hinv184 s184 v189 v192
  store_step with Store.apply_rep s185 v186 v193 _ _ hinv185 h64 h_v186 h_v193 (by ns_tac) (by ns_tac) as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v183 dropping h_v186 h_v193 hinv185 s185 v186 v193
  store_step with Store.apply_rep s186 v183 v194 _ _ hinv186 h64 h_v183 h_v194 (by ns_tac) (by ns_tac) as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 dropping h_v183 h_v194 hinv186 s186 v183 v194
  step as ⟨e_v196, he_v196⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s187 e_v196 (by rw [he_v196]; exact empty_args) hinv187 h64 as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 dropping he_v196 hinv187 e_v196 s187
  store_step with Store.apply_rep s188 v196 v8 _ _ hinv188 h64 h_v196 h_v8 (by ns_tac) (by ns_tac) as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 dropping h_v196 hinv188 s188 v196
  store_step with Store.apply_rep s189 v197 v5 _ _ hinv189 h64 h_v197 h_v5 (by ns_tac) (by ns_tac) as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 dropping h_v197 hinv189 s189 v197
  step as ⟨e_v199, he_v199⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s190 _ _ rfl hinv190 h64 as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 h_v198 dropping hinv190 s190
  replace h_v199 := Represents.rep_of_eq h_v199 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v199]; decide)
  step as ⟨e_v200, he_v200⟩
  store_step with CtorSpec.eo_Int.construct s191 e_v200 (by rw [he_v200]; exact empty_args) hinv191 h64 as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 h_v198 h_v199 dropping he_v199 he_v200 hinv191 e_v199 e_v200 s191
  step as ⟨e_v201, he_v201⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s192 e_v201 (by rw [he_v201]; rfl) h_v199 h_v200 hinv192 h64 as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 h_v198 dropping h_v199 h_v200 he_v201 hinv192 e_v201 s192 v199 v200
  store_step with Store.apply_rep s193 v198 v201 _ _ hinv193 h64 h_v198 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 h_v195 dropping h_v198 h_v201 hinv193 s193 v198 v201
  store_step with Store.apply_rep s194 v195 v202 _ _ hinv194 h64 h_v195 h_v202 (by ns_tac) (by ns_tac) as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 h_v182 dropping h_v195 h_v202 hinv194 s194 v195 v202
  store_step with Store.apply_rep s195 v182 v203 _ _ hinv195 h64 h_v182 h_v203 (by ns_tac) (by ns_tac) as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v172 dropping h_v182 h_v203 hinv195 s195 v182 v203
  store_step with Store.apply_rep s196 v172 v204 _ _ hinv196 h64 h_v172 h_v204 (by ns_tac) (by ns_tac) as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 dropping h_v172 h_v204 hinv196 s196 v172 v204
  step as ⟨e_v206, he_v206⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s197 e_v206 (by rw [he_v206]; exact empty_args) hinv197 h64 as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 dropping he_v206 hinv197 e_v206 s197
  store_step with Store.apply_rep s198 v206 v2 _ _ hinv198 h64 h_v206 h_v2 (by ns_tac) (by ns_tac) as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 dropping h_v206 hinv198 s198 v206
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s199 e_v208 (by rw [he_v208]; exact empty_args) hinv199 h64 as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 dropping he_v208 hinv199 e_v208 s199
  step as ⟨e_v209, he_v209⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct s200 e_v209 (by rw [he_v209]; exact empty_args) hinv200 h64 as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 dropping he_v209 hinv200 e_v209 s200
  store_step with Store.apply_rep s201 v209 v8 _ _ hinv201 h64 h_v209 h_v8 (by ns_tac) (by ns_tac) as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 dropping h_v209 hinv201 s201 v209
  store_step with Store.apply_rep s202 v210 v5 _ _ hinv202 h64 h_v210 h_v5 (by ns_tac) (by ns_tac) as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 dropping h_v210 hinv202 s202 v210
  store_step with Store.apply_rep s203 v211 v2 _ _ hinv203 h64 h_v211 h_v2 (by ns_tac) (by ns_tac) as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 dropping h_v2 h_v211 hinv203 s203 v2 v211
  step as ⟨e_v213, he_v213⟩
  store_step with CtorSpec.eo__2b.construct s204 e_v213 (by rw [he_v213]; exact empty_args) hinv204 h64 as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 dropping he_v213 hinv204 e_v213 s204
  step as ⟨e_v214, he_v214⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s205 _ _ rfl hinv205 h64 as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v213 dropping hinv205 s205
  replace h_v214 := Represents.rep_of_eq h_v214 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v214]; decide)
  step as ⟨e_v215, he_v215⟩
  store_step with CtorSpec.eo_Int.construct s206 e_v215 (by rw [he_v215]; exact empty_args) hinv206 h64 as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v213 h_v214 dropping he_v214 he_v215 hinv206 e_v214 e_v215 s206
  step as ⟨e_v216, he_v216⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s207 e_v216 (by rw [he_v216]; rfl) h_v214 h_v215 hinv207 h64 as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v213 dropping h_v214 h_v215 he_v216 hinv207 e_v216 s207 v214 v215
  store_step with Store.apply_rep s208 v213 v216 _ _ hinv208 h64 h_v213 h_v216 (by ns_tac) (by ns_tac) as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 dropping h_v213 h_v216 hinv208 s208 v213 v216
  step as ⟨e_v218, he_v218⟩
  store_step with CtorSpec.eo__2b.construct s209 e_v218 (by rw [he_v218]; exact empty_args) hinv209 h64 as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v217 dropping he_v218 hinv209 e_v218 s209
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s210 1#u32 (1) (by scalar_tac) hinv210 h64 as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v217 h_v218 dropping hinv210 s210
  store_step with Store.apply_rep s211 v218 v219 _ _ hinv211 h64 h_v218 h_v219 (by ns_tac) (by ns_tac) as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v217 dropping h_v218 h_v219 hinv211 s211 v218 v219
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s212 0#u32 (0) (by scalar_tac) hinv212 h64 as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v217 h_v220 dropping hinv212 s212
  store_step with Store.apply_rep s213 v220 v221 _ _ hinv213 h64 h_v220 h_v221 (by ns_tac) (by ns_tac) as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 h_v217 dropping h_v220 h_v221 hinv213 s213 v220 v221
  store_step with Store.apply_rep s214 v217 v222 _ _ hinv214 h64 h_v217 h_v222 (by ns_tac) (by ns_tac) as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 h_v212 dropping h_v217 h_v222 hinv214 s214 v217 v222
  store_step with Store.apply_rep s215 v212 v223 _ _ hinv215 h64 h_v212 h_v223 (by ns_tac) (by ns_tac) as ⟨v224, s216, hinv216, h_v224⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v208 dropping h_v212 h_v223 hinv215 s215 v212 v223
  store_step with Store.apply_rep s216 v208 v224 _ _ hinv216 h64 h_v208 h_v224 (by ns_tac) (by ns_tac) as ⟨v225, s217, hinv217, h_v225⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 dropping h_v208 h_v224 hinv216 s216 v208 v224
  step as ⟨e_v226, he_v226⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s217 e_v226 (by rw [he_v226]; exact empty_args) hinv217 h64 as ⟨v226, s218, hinv218, h_v226⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 dropping he_v226 hinv217 e_v226 s217
  step as ⟨e_v227, he_v227⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s218 e_v227 (by rw [he_v227]; exact empty_args) hinv218 h64 as ⟨v227, s219, hinv219, h_v227⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 dropping he_v227 hinv218 e_v227 s218
  store_step with Store.apply_rep s219 v227 v8 _ _ hinv219 h64 h_v227 h_v8 (by ns_tac) (by ns_tac) as ⟨v228, s220, hinv220, h_v228⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 dropping h_v227 hinv219 s219 v227
  step as ⟨e_v229, he_v229⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s220 e_v229 (by rw [he_v229]; exact empty_args) hinv220 h64 as ⟨v229, s221, hinv221, h_v229⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 dropping he_v229 hinv220 e_v229 s220
  store_step with Store.apply_rep s221 v229 v8 _ _ hinv221 h64 h_v229 h_v8 (by ns_tac) (by ns_tac) as ⟨v230, s222, hinv222, h_v230⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 dropping h_v229 hinv221 s221 v229
  store_step with Store.apply_rep s222 v230 v5 _ _ hinv222 h64 h_v230 h_v5 (by ns_tac) (by ns_tac) as ⟨v231, s223, hinv223, h_v231⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 dropping h_v230 hinv222 s222 v230
  step as ⟨e_v232, he_v232⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s223 _ _ rfl hinv223 h64 as ⟨v232, s224, hinv224, h_v232⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 h_v231 dropping hinv223 s223
  replace h_v232 := Represents.rep_of_eq h_v232 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v232]; decide)
  step as ⟨e_v233, he_v233⟩
  store_step with CtorSpec.eo_Int.construct s224 e_v233 (by rw [he_v233]; exact empty_args) hinv224 h64 as ⟨v233, s225, hinv225, h_v233⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 h_v231 h_v232 dropping he_v232 he_v233 hinv224 e_v232 e_v233 s224
  step as ⟨e_v234, he_v234⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s225 e_v234 (by rw [he_v234]; rfl) h_v232 h_v233 hinv225 h64 as ⟨v234, s226, hinv226, h_v234⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 h_v231 dropping h_v232 h_v233 he_v234 hinv225 e_v234 s225 v232 v233
  store_step with Store.apply_rep s226 v231 v234 _ _ hinv226 h64 h_v231 h_v234 (by ns_tac) (by ns_tac) as ⟨v235, s227, hinv227, h_v235⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v228 dropping h_v231 h_v234 hinv226 s226 v231 v234
  store_step with Store.apply_rep s227 v228 v235 _ _ hinv227 h64 h_v228 h_v235 (by ns_tac) (by ns_tac) as ⟨v236, s228, hinv228, h_v236⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 dropping h_v228 h_v235 hinv227 s227 v228 v235
  step as ⟨e_v237, he_v237⟩
  store_step with CtorSpec.eo__2d.construct s228 e_v237 (by rw [he_v237]; exact empty_args) hinv228 h64 as ⟨v237, s229, hinv229, h_v237⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 dropping he_v237 hinv228 e_v237 s228
  step as ⟨e_v238, he_v238⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s229 e_v238 (by rw [he_v238]; exact empty_args) hinv229 h64 as ⟨v238, s230, hinv230, h_v238⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 dropping he_v238 hinv229 e_v238 s229
  store_step with Store.apply_rep s230 v238 v8 _ _ hinv230 h64 h_v238 h_v8 (by ns_tac) (by ns_tac) as ⟨v239, s231, hinv231, h_v239⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 dropping h_v238 hinv230 s230 v238
  store_step with Store.apply_rep s231 v239 v5 _ _ hinv231 h64 h_v239 h_v5 (by ns_tac) (by ns_tac) as ⟨v240, s232, hinv232, h_v240⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 dropping h_v239 hinv231 s231 v239
  step as ⟨e_v241, he_v241⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s232 e_v241 (by rw [he_v241]; exact empty_args) hinv232 h64 as ⟨v241, s233, hinv233, h_v241⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 dropping he_v241 hinv232 e_v241 s232
  store_step with Store.apply_rep s233 v241 v8 _ _ hinv233 h64 h_v241 h_v8 (by ns_tac) (by ns_tac) as ⟨v242, s234, hinv234, h_v242⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 dropping h_v241 hinv233 s233 v241
  store_step with Store.apply_rep s234 v242 v5 _ _ hinv234 h64 h_v242 h_v5 (by ns_tac) (by ns_tac) as ⟨v243, s235, hinv235, h_v243⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 dropping h_v242 hinv234 s234 v242
  step as ⟨e_v244, he_v244⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s235 _ _ rfl hinv235 h64 as ⟨v244, s236, hinv236, h_v244⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 h_v243 dropping hinv235 s235
  replace h_v244 := Represents.rep_of_eq h_v244 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v244]; decide)
  step as ⟨e_v245, he_v245⟩
  store_step with CtorSpec.eo_Int.construct s236 e_v245 (by rw [he_v245]; exact empty_args) hinv236 h64 as ⟨v245, s237, hinv237, h_v245⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 h_v243 h_v244 dropping he_v244 he_v245 hinv236 e_v244 e_v245 s236
  step as ⟨e_v246, he_v246⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s237 e_v246 (by rw [he_v246]; rfl) h_v244 h_v245 hinv237 h64 as ⟨v246, s238, hinv238, h_v246⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 h_v243 dropping h_v244 h_v245 he_v246 hinv237 e_v246 s237 v244 v245
  store_step with Store.apply_rep s238 v243 v246 _ _ hinv238 h64 h_v243 h_v246 (by ns_tac) (by ns_tac) as ⟨v247, s239, hinv239, h_v247⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 h_v240 dropping h_v243 h_v246 hinv238 s238 v243 v246
  store_step with Store.apply_rep s239 v240 v247 _ _ hinv239 h64 h_v240 h_v247 (by ns_tac) (by ns_tac) as ⟨v248, s240, hinv240, h_v248⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v237 dropping h_v240 h_v247 hinv239 s239 v240 v247
  store_step with Store.apply_rep s240 v237 v248 _ _ hinv240 h64 h_v237 h_v248 (by ns_tac) (by ns_tac) as ⟨v249, s241, hinv241, h_v249⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 dropping h_v237 h_v248 hinv240 s240 v237 v248
  step as ⟨e_v250, he_v250⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s241 e_v250 (by rw [he_v250]; exact empty_args) hinv241 h64 as ⟨v250, s242, hinv242, h_v250⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 dropping he_v250 hinv241 e_v250 s241
  store_step with Store.apply_rep s242 v250 v8 _ _ hinv242 h64 h_v250 h_v8 (by ns_tac) (by ns_tac) as ⟨v251, s243, hinv243, h_v251⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 dropping h_v250 hinv242 s242 v250
  store_step with Store.apply_rep s243 v251 v5 _ _ hinv243 h64 h_v251 h_v5 (by ns_tac) (by ns_tac) as ⟨v252, s244, hinv244, h_v252⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 dropping h_v251 hinv243 s243 v251
  step as ⟨e_v253, he_v253⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s244 _ _ rfl hinv244 h64 as ⟨v253, s245, hinv245, h_v253⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 h_v252 dropping hinv244 s244
  replace h_v253 := Represents.rep_of_eq h_v253 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v253]; decide)
  step as ⟨e_v254, he_v254⟩
  store_step with CtorSpec.eo_Int.construct s245 e_v254 (by rw [he_v254]; exact empty_args) hinv245 h64 as ⟨v254, s246, hinv246, h_v254⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 h_v252 h_v253 dropping he_v253 he_v254 hinv245 e_v253 e_v254 s245
  step as ⟨e_v255, he_v255⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s246 e_v255 (by rw [he_v255]; rfl) h_v253 h_v254 hinv246 h64 as ⟨v255, s247, hinv247, h_v255⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 h_v252 dropping h_v253 h_v254 he_v255 hinv246 e_v255 s246 v253 v254
  store_step with Store.apply_rep s247 v252 v255 _ _ hinv247 h64 h_v252 h_v255 (by ns_tac) (by ns_tac) as ⟨v256, s248, hinv248, h_v256⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 h_v249 dropping h_v252 h_v255 hinv247 s247 v252 v255
  store_step with Store.apply_rep s248 v249 v256 _ _ hinv248 h64 h_v249 h_v256 (by ns_tac) (by ns_tac) as ⟨v257, s249, hinv249, h_v257⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 h_v236 dropping h_v249 h_v256 hinv248 s248 v249 v256
  store_step with Store.apply_rep s249 v236 v257 _ _ hinv249 h64 h_v236 h_v257 (by ns_tac) (by ns_tac) as ⟨v258, s250, hinv250, h_v258⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 dropping h_v236 h_v257 hinv249 s249 v236 v257
  store_step with ih.eo__24eo_5ftypeof s250 v258 _ hinv250 h64 (hG.rem hrem) h_v258 as ⟨v259, s251, hinv251, h_v259⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 h_v226 dropping h_v258 hinv250 s250 v258
  store_step with ih.eo__24eo_5fnil s251 v226 v259 _ _ hinv251 h64 (hG.rem hrem) h_v226 h_v259 as ⟨v260, s252, hinv252, h_v260⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 h_v225 dropping h_v226 h_v259 hinv251 s251 v226 v259
  store_step with Store.apply_mk_rep s252 v225 v260 _ _ hinv252 h64 h_v225 h_v260 as ⟨v261, s253, hinv253, h_v261⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 h_v207 dropping h_v225 h_v260 hinv252 s252 v225 v260
  store_step with Store.apply_mk_rep s253 v207 v261 _ _ hinv253 h64 h_v207 h_v261 as ⟨v262, s254, hinv254, h_v262⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 h_v205 dropping h_v207 h_v261 hinv253 s253 v207 v261
  store_step with Store.apply_mk_rep s254 v205 v262 _ _ hinv254 h64 h_v205 h_v262 as ⟨v263, s255, hinv255, h_v263⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 h_v171 dropping h_v205 h_v262 hinv254 s254 v205 v262
  store_step with Store.apply_mk_rep s255 v171 v263 _ _ hinv255 h64 h_v171 h_v263 as ⟨v264, s256, hinv256, h_v264⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v161 dropping h_v171 h_v263 hinv255 s255 v171 v263
  store_step with Store.apply_mk_rep s256 v161 v264 _ _ hinv256 h64 h_v161 h_v264 as ⟨v265, s257, hinv257, h_v265⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 dropping h_v161 h_v264 hinv256 s256 v161 v264
  step as ⟨e_v266, he_v266⟩
  store_step with CtorSpec.eo_and.construct s257 e_v266 (by rw [he_v266]; exact empty_args) hinv257 h64 as ⟨v266, s258, hinv258, h_v266⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 dropping he_v266 hinv257 e_v266 s257
  step as ⟨e_v267, he_v267⟩
  store_step with CtorSpec.eo__3d.construct s258 e_v267 (by rw [he_v267]; exact empty_args) hinv258 h64 as ⟨v267, s259, hinv259, h_v267⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 dropping he_v267 hinv258 e_v267 s258
  step as ⟨e_v268, he_v268⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s259 e_v268 (by rw [he_v268]; exact empty_args) hinv259 h64 as ⟨v268, s260, hinv260, h_v268⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 dropping he_v268 hinv259 e_v268 s259
  store_step with Store.apply_rep s260 v268 v8 _ _ hinv260 h64 h_v268 h_v8 (by ns_tac) (by ns_tac) as ⟨v269, s261, hinv261, h_v269⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 dropping h_v268 hinv260 s260 v268
  store_step with Store.apply_rep s261 v269 v5 _ _ hinv261 h64 h_v269 h_v5 (by ns_tac) (by ns_tac) as ⟨v270, s262, hinv262, h_v270⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 dropping h_v269 hinv261 s261 v269
  step as ⟨e_v271, he_v271⟩
  store_step with CtorSpec.eo__2b.construct s262 e_v271 (by rw [he_v271]; exact empty_args) hinv262 h64 as ⟨v271, s263, hinv263, h_v271⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 dropping he_v271 hinv262 e_v271 s262
  step as ⟨e_v272, he_v272⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s263 _ _ rfl hinv263 h64 as ⟨v272, s264, hinv264, h_v272⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v271 dropping hinv263 s263
  replace h_v272 := Represents.rep_of_eq h_v272 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v272]; decide)
  step as ⟨e_v273, he_v273⟩
  store_step with CtorSpec.eo_Int.construct s264 e_v273 (by rw [he_v273]; exact empty_args) hinv264 h64 as ⟨v273, s265, hinv265, h_v273⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v271 h_v272 dropping he_v272 he_v273 hinv264 e_v272 e_v273 s264
  step as ⟨e_v274, he_v274⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s265 e_v274 (by rw [he_v274]; rfl) h_v272 h_v273 hinv265 h64 as ⟨v274, s266, hinv266, h_v274⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v271 dropping h_v272 h_v273 he_v274 hinv265 e_v274 s265 v272 v273
  store_step with Store.apply_rep s266 v271 v274 _ _ hinv266 h64 h_v271 h_v274 (by ns_tac) (by ns_tac) as ⟨v275, s267, hinv267, h_v275⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 dropping h_v271 h_v274 hinv266 s266 v271 v274
  step as ⟨e_v276, he_v276⟩
  store_step with CtorSpec.eo__2b.construct s267 e_v276 (by rw [he_v276]; exact empty_args) hinv267 h64 as ⟨v276, s268, hinv268, h_v276⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v275 dropping he_v276 hinv267 e_v276 s267
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s268 1#u32 (1) (by scalar_tac) hinv268 h64 as ⟨v277, s269, hinv269, h_v277⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v275 h_v276 dropping hinv268 s268
  store_step with Store.apply_rep s269 v276 v277 _ _ hinv269 h64 h_v276 h_v277 (by ns_tac) (by ns_tac) as ⟨v278, s270, hinv270, h_v278⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v275 dropping h_v276 h_v277 hinv269 s269 v276 v277
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s270 0#u32 (0) (by scalar_tac) hinv270 h64 as ⟨v279, s271, hinv271, h_v279⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v275 h_v278 dropping hinv270 s270
  store_step with Store.apply_rep s271 v278 v279 _ _ hinv271 h64 h_v278 h_v279 (by ns_tac) (by ns_tac) as ⟨v280, s272, hinv272, h_v280⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 h_v275 dropping h_v278 h_v279 hinv271 s271 v278 v279
  store_step with Store.apply_rep s272 v275 v280 _ _ hinv272 h64 h_v275 h_v280 (by ns_tac) (by ns_tac) as ⟨v281, s273, hinv273, h_v281⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 h_v270 dropping h_v275 h_v280 hinv272 s272 v275 v280
  store_step with Store.apply_rep s273 v270 v281 _ _ hinv273 h64 h_v270 h_v281 (by ns_tac) (by ns_tac) as ⟨v282, s274, hinv274, h_v282⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v267 dropping h_v270 h_v281 hinv273 s273 v270 v281
  store_step with Store.apply_rep s274 v267 v282 _ _ hinv274 h64 h_v267 h_v282 (by ns_tac) (by ns_tac) as ⟨v283, s275, hinv275, h_v283⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 dropping h_v267 h_v282 hinv274 s274 v267 v282
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo__2b.construct s275 e_v284 (by rw [he_v284]; exact empty_args) hinv275 h64 as ⟨v284, s276, hinv276, h_v284⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 dropping he_v284 hinv275 e_v284 s275
  step as ⟨e_v285, he_v285⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s276 e_v285 (by rw [he_v285]; exact empty_args) hinv276 h64 as ⟨v285, s277, hinv277, h_v285⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 dropping he_v285 hinv276 e_v285 s276
  store_step with Store.apply_rep s277 v285 v8 _ _ hinv277 h64 h_v285 h_v8 (by ns_tac) (by ns_tac) as ⟨v286, s278, hinv278, h_v286⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 dropping h_v285 hinv277 s277 v285
  store_step with Store.apply_rep s278 v286 v5 _ _ hinv278 h64 h_v286 h_v5 (by ns_tac) (by ns_tac) as ⟨v287, s279, hinv279, h_v287⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 dropping h_v286 hinv278 s278 v286
  step as ⟨e_v288, he_v288⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex.construct s279 e_v288 (by rw [he_v288]; exact empty_args) hinv279 h64 as ⟨v288, s280, hinv280, h_v288⟩ growing hG carrying h_v5 h_v8 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 dropping he_v288 hinv279 e_v288 s279
  store_step with Store.apply_rep s280 v288 v8 _ _ hinv280 h64 h_v288 h_v8 (by ns_tac) (by ns_tac) as ⟨v289, s281, hinv281, h_v289⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 dropping h_v288 h_v8 hinv280 s280 v288 v8
  store_step with Store.apply_rep s281 v289 v5 _ _ hinv281 h64 h_v289 h_v5 (by ns_tac) (by ns_tac) as ⟨v290, s282, hinv282, h_v290⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 dropping h_v289 hinv281 s281 v289
  step as ⟨e_v291, he_v291⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s282 _ _ rfl hinv282 h64 as ⟨v291, s283, hinv283, h_v291⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 h_v290 dropping hinv282 s282
  replace h_v291 := Represents.rep_of_eq h_v291 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v291]; decide)
  step as ⟨e_v292, he_v292⟩
  store_step with CtorSpec.eo_Int.construct s283 e_v292 (by rw [he_v292]; exact empty_args) hinv283 h64 as ⟨v292, s284, hinv284, h_v292⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 h_v290 h_v291 dropping he_v291 he_v292 hinv283 e_v291 e_v292 s283
  step as ⟨e_v293, he_v293⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s284 e_v293 (by rw [he_v293]; rfl) h_v291 h_v292 hinv284 h64 as ⟨v293, s285, hinv285, h_v293⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 h_v290 dropping h_v291 h_v292 he_v293 hinv284 e_v293 s284 v291 v292
  store_step with Store.apply_rep s285 v290 v293 _ _ hinv285 h64 h_v290 h_v293 (by ns_tac) (by ns_tac) as ⟨v294, s286, hinv286, h_v294⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 h_v287 dropping h_v290 h_v293 hinv285 s285 v290 v293
  store_step with Store.apply_rep s286 v287 v294 _ _ hinv286 h64 h_v287 h_v294 (by ns_tac) (by ns_tac) as ⟨v295, s287, hinv287, h_v295⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v284 dropping h_v287 h_v294 hinv286 s286 v287 v294
  store_step with Store.apply_rep s287 v284 v295 _ _ hinv287 h64 h_v284 h_v295 (by ns_tac) (by ns_tac) as ⟨v296, s288, hinv288, h_v296⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 dropping h_v284 h_v295 hinv287 s287 v284 v295
  step as ⟨e_v297, he_v297⟩
  store_step with CtorSpec.eo__2b.construct s288 e_v297 (by rw [he_v297]; exact empty_args) hinv288 h64 as ⟨v297, s289, hinv289, h_v297⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v296 dropping he_v297 hinv288 e_v297 s288
  step as ⟨e_v298, he_v298⟩
  store_step with CtorSpec.eo_str_2elen.construct s289 e_v298 (by rw [he_v298]; exact empty_args) hinv289 h64 as ⟨v298, s290, hinv290, h_v298⟩ growing hG carrying h_v5 h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v296 h_v297 dropping he_v298 hinv289 e_v298 s289
  store_step with Store.apply_rep s290 v298 v5 _ _ hinv290 h64 h_v298 h_v5 (by ns_tac) (by ns_tac) as ⟨v299, s291, hinv291, h_v299⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v296 h_v297 dropping h_v298 h_v5 hinv290 s290 v298 v5
  store_step with Store.apply_rep s291 v297 v299 _ _ hinv291 h64 h_v297 h_v299 (by ns_tac) (by ns_tac) as ⟨v300, s292, hinv292, h_v300⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v296 dropping h_v297 h_v299 hinv291 s291 v297 v299
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s292 0#u32 (0) (by scalar_tac) hinv292 h64 as ⟨v301, s293, hinv293, h_v301⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v296 h_v300 dropping hinv292 s292
  store_step with Store.apply_rep s293 v300 v301 _ _ hinv293 h64 h_v300 h_v301 (by ns_tac) (by ns_tac) as ⟨v302, s294, hinv294, h_v302⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 h_v296 dropping h_v300 h_v301 hinv293 s293 v300 v301
  store_step with Store.apply_rep s294 v296 v302 _ _ hinv294 h64 h_v296 h_v302 (by ns_tac) (by ns_tac) as ⟨v303, s295, hinv295, h_v303⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 h_v283 dropping h_v296 h_v302 hinv294 s294 v296 v302
  store_step with Store.apply_rep s295 v283 v303 _ _ hinv295 h64 h_v283 h_v303 (by ns_tac) (by ns_tac) as ⟨v304, s296, hinv296, h_v304⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v266 dropping h_v283 h_v303 hinv295 s295 v283 v303
  store_step with Store.apply_rep s296 v266 v304 _ _ hinv296 h64 h_v266 h_v304 (by ns_tac) (by ns_tac) as ⟨v305, s297, hinv297, h_v305⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 dropping h_v266 h_v304 hinv296 s296 v266 v304
  store_step with Store.literal_boolean_spec s297 true hinv297 h64 as ⟨v306, s298, hinv298, h_v306⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 h_v305 dropping hinv297 s297
  store_step with Store.apply_rep s298 v305 v306 _ _ hinv298 h64 h_v305 h_v306 (by ns_tac) (by ns_tac) as ⟨v307, s299, hinv299, h_v307⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 h_v265 dropping h_v305 h_v306 hinv298 s298 v305 v306
  store_step with Store.apply_mk_rep s299 v265 v307 _ _ hinv299 h64 h_v265 h_v307 as ⟨v308, s300, hinv300, h_v308⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 h_v160 dropping h_v265 h_v307 hinv299 s299 v265 v307
  store_step with Store.apply_mk_rep s300 v160 v308 _ _ hinv300 h64 h_v160 h_v308 as ⟨v309, s301, hinv301, h_v309⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v141 dropping h_v160 h_v308 hinv300 s300 v160 v308
  store_step with Store.apply_mk_rep s301 v141 v309 _ _ hinv301 h64 h_v141 h_v309 as ⟨v310, s302, hinv302, h_v310⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 dropping h_v141 h_v309 hinv301 s301 v141 v309
  store_step with Store.literal_boolean_spec s302 false hinv302 h64 as ⟨v311, s303, hinv303, h_v311⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 h_v310 dropping hinv302 s302
  store_step with Store.apply_mk_rep s303 v310 v311 _ _ hinv303 h64 h_v310 h_v311 as ⟨v312, s304, hinv304, h_v312⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 h_v140 dropping h_v310 h_v311 hinv303 s303 v310 v311
  store_step with Store.apply_mk_rep s304 v140 v312 _ _ hinv304 h64 h_v140 h_v312 as ⟨v313, s305, hinv305, h_v313⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 h_v127 dropping h_v140 h_v312 hinv304 s304 v140 v312
  store_step with Store.apply_mk_rep s305 v127 v313 _ _ hinv305 h64 h_v127 h_v313 as ⟨v314, s306, hinv306, h_v314⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 h_v116 dropping h_v127 h_v313 hinv305 s305 v127 v313
  store_step with Store.apply_mk_rep s306 v116 v314 _ _ hinv306 h64 h_v116 h_v314 as ⟨v315, s307, hinv307, h_v315⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v107 dropping h_v116 h_v314 hinv306 s306 v116 v314
  store_step with Store.apply_mk_rep s307 v107 v315 _ _ hinv307 h64 h_v107 h_v315 as ⟨v316, s308, hinv308, h_v316⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 dropping h_v107 h_v315 hinv307 s307 v107 v315
  store_step with Store.literal_boolean_spec s308 true hinv308 h64 as ⟨v317, s309, hinv309, h_v317⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 h_v316 dropping hinv308 s308
  store_step with Store.apply_mk_rep s309 v316 v317 _ _ hinv309 h64 h_v316 h_v317 as ⟨v318, s310, hinv310, h_v318⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 h_v106 dropping h_v316 h_v317 hinv309 s309 v316 v317
  store_step with Store.apply_mk_rep s310 v106 v318 _ _ hinv310 h64 h_v106 h_v318 as ⟨v319, s311, hinv311, h_v319⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 h_v89 dropping h_v106 h_v318 hinv310 s310 v106 v318
  store_step with Store.apply_mk_rep s311 v89 v319 _ _ hinv311 h64 h_v89 h_v319 as ⟨v320, s312, hinv312, h_v320⟩ growing hG carrying h_v26 h_v35 h_v52 h_v78 dropping h_v319 h_v89 hinv311 s311 v319 v89
  store_step with Store.apply_mk_rep s312 v78 v320 _ _ hinv312 h64 h_v78 h_v320 as ⟨v321, s313, hinv313, h_v321⟩ growing hG carrying h_v26 h_v35 h_v52 dropping h_v320 h_v78 hinv312 s312 v320 v78
  store_step with Store.apply_mk_rep s313 v52 v321 _ _ hinv313 h64 h_v52 h_v321 as ⟨v322, s314, hinv314, h_v322⟩ growing hG carrying h_v26 h_v35 dropping h_v321 h_v52 hinv313 s313 v321 v52
  store_step with Store.apply_mk_rep s314 v35 v322 _ _ hinv314 h64 h_v35 h_v322 as ⟨v323, s315, hinv315, h_v323⟩ growing hG carrying h_v26 dropping h_v322 h_v35 hinv314 s314 v322 v35
  store_step with Store.apply_mk_rep s315 v26 v323 _ _ hinv315 h64 h_v26 h_v323 as ⟨v324, s316, hinv316, h_v324⟩ growing hG carrying dropping h_v26 h_v323 hinv315 s315 v26 v323
  case_done hinv316 hG with h_v324 in EoCases.__str_reduction_pred.case_8 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

set_option maxHeartbeats 10020000 in
theorem case_9_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_9_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_9
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_9
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_9
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_9
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s3 _ _ rfl hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping hinv3 s3
  store_step with Store.apply_rep s4 v11 v12 _ _ hinv4 h64 h_v11 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 h_v12 hinv4 s4 v11 v12
  store_step with Store.apply_rep s5 v13 v5 _ _ hinv5 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v13 hinv5 s5 v13
  store_step with Store.apply_rep s6 v10 v14 _ _ hinv6 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v14 hinv6 s6 v10 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 dropping he_v16 hinv7 e_v16 s7
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__40purify.construct s8 e_v17 (by rw [he_v17]; exact empty_args) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v16 dropping he_v17 hinv8 e_v17 s8
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s9 e_v18 (by rw [he_v18]; exact empty_args) hinv9 h64 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v16 h_v17 dropping he_v18 hinv9 e_v18 s9
  store_step with Store.apply_rep s10 v18 v8 _ _ hinv10 h64 h_v18 h_v8 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v16 h_v17 dropping h_v18 hinv10 s10 v18
  store_step with Store.apply_rep s11 v19 v5 _ _ hinv11 h64 h_v19 h_v5 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v16 h_v17 dropping h_v19 hinv11 s11 v19
  store_step with Store.apply_rep s12 v20 v2 _ _ hinv12 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v16 h_v17 dropping h_v20 hinv12 s12 v20
  store_step with Store.apply_rep s13 v17 v21 _ _ hinv13 h64 h_v17 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v16 dropping h_v17 h_v21 hinv13 s13 v17 v21
  store_step with Store.apply_rep s14 v16 v22 _ _ hinv14 h64 h_v16 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 dropping h_v16 h_v22 hinv14 s14 v16 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s15 e_v24 (by rw [he_v24]; exact empty_args) hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 dropping he_v24 hinv15 e_v24 s15
  store_step with Store.apply_rep s16 v24 v2 _ _ hinv16 h64 h_v24 h_v2 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 dropping h_v24 hinv16 s16 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v26 (by rw [he_v26]; exact empty_args) hinv17 h64 as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 h_v25 dropping he_v26 hinv17 e_v26 s17
  store_step with Store.apply_rep s18 v26 v8 _ _ hinv18 h64 h_v26 h_v8 (by ns_tac) (by ns_tac) as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 h_v25 dropping h_v26 hinv18 s18 v26
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s19 _ _ rfl hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 h_v25 h_v27 dropping hinv19 s19
  store_step with Store.apply_rep s20 v27 v28 _ _ hinv20 h64 h_v27 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 h_v25 dropping h_v27 h_v28 hinv20 s20 v27 v28
  store_step with Store.apply_rep s21 v25 v29 _ _ hinv21 h64 h_v25 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 h_v23 dropping h_v25 h_v29 hinv21 s21 v25 v29
  store_step with Store.apply_rep s22 v23 v30 _ _ hinv22 h64 h_v23 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v15 dropping h_v23 h_v30 hinv22 s22 v23 v30
  store_step with Store.apply_rep s23 v15 v31 _ _ hinv23 h64 h_v15 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v15 h_v31 hinv23 s23 v15 v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_ite.construct s24 e_v33 (by rw [he_v33]; exact empty_args) hinv24 h64 as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 dropping he_v33 hinv24 e_v33 s24
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s25 e_v34 (by rw [he_v34]; exact empty_args) hinv25 h64 as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 dropping he_v34 hinv25 e_v34 s25
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s26 e_v35 (by rw [he_v35]; exact empty_args) hinv26 h64 as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 h_v34 dropping he_v35 hinv26 e_v35 s26
  store_step with Store.apply_rep s27 v35 v8 _ _ hinv27 h64 h_v35 h_v8 (by ns_tac) (by ns_tac) as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 h_v34 dropping h_v35 hinv27 s27 v35
  store_step with Store.apply_rep s28 v36 v5 _ _ hinv28 h64 h_v36 h_v5 (by ns_tac) (by ns_tac) as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 h_v34 dropping h_v36 hinv28 s28 v36
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 0#u32 (0) (by scalar_tac) hinv29 h64 as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 h_v34 h_v37 dropping hinv29 s29
  store_step with Store.apply_rep s30 v37 v38 _ _ hinv30 h64 h_v37 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 h_v34 dropping h_v37 h_v38 hinv30 s30 v37 v38
  store_step with Store.apply_rep s31 v34 v39 _ _ hinv31 h64 h_v34 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 dropping h_v34 h_v39 hinv31 s31 v34 v39
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s32 1#u32 (-1) (by scalar_tac) hinv32 h64 as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 h_v40 dropping hinv32 s32
  store_step with Store.apply_rep s33 v40 v41 _ _ hinv33 h64 h_v40 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v33 dropping h_v40 h_v41 hinv33 s33 v40 v41
  store_step with Store.apply_rep s34 v33 v42 _ _ hinv34 h64 h_v33 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 dropping h_v33 h_v42 hinv34 s34 v33 v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3d.construct s35 e_v44 (by rw [he_v44]; exact empty_args) hinv35 h64 as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 dropping he_v44 hinv35 e_v44 s35
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__40purify.construct s36 e_v45 (by rw [he_v45]; exact empty_args) hinv36 h64 as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 h_v44 dropping he_v45 hinv36 e_v45 s36
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s37 e_v46 (by rw [he_v46]; exact empty_args) hinv37 h64 as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 h_v44 h_v45 dropping he_v46 hinv37 e_v46 s37
  store_step with Store.apply_rep s38 v46 v8 _ _ hinv38 h64 h_v46 h_v8 (by ns_tac) (by ns_tac) as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 h_v44 h_v45 dropping h_v46 hinv38 s38 v46
  store_step with Store.apply_rep s39 v47 v5 _ _ hinv39 h64 h_v47 h_v5 (by ns_tac) (by ns_tac) as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 h_v44 h_v45 dropping h_v47 hinv39 s39 v47
  store_step with Store.apply_rep s40 v48 v2 _ _ hinv40 h64 h_v48 h_v2 (by ns_tac) (by ns_tac) as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 h_v44 h_v45 dropping h_v48 hinv40 s40 v48
  store_step with Store.apply_rep s41 v45 v49 _ _ hinv41 h64 h_v45 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 h_v44 dropping h_v45 h_v49 hinv41 s41 v45 v49
  store_step with Store.apply_rep s42 v44 v50 _ _ hinv42 h64 h_v44 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 dropping h_v44 h_v50 hinv42 s42 v44 v50
  store_step with Store.apply_rep s43 v51 v8 _ _ hinv43 h64 h_v51 h_v8 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v43 dropping h_v51 hinv43 s43 v51
  store_step with Store.apply_rep s44 v43 v52 _ _ hinv44 h64 h_v43 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 dropping h_v43 h_v52 hinv44 s44 v43 v52
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_and.construct s45 e_v54 (by rw [he_v54]; exact empty_args) hinv45 h64 as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 dropping he_v54 hinv45 e_v54 s45
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__3d.construct s46 e_v55 (by rw [he_v55]; exact empty_args) hinv46 h64 as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 dropping he_v55 hinv46 e_v55 s46
  store_step with Store.apply_rep s47 v55 v8 _ _ hinv47 h64 h_v55 h_v8 (by ns_tac) (by ns_tac) as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 dropping h_v55 hinv47 s47 v55
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s48 e_v57 (by rw [he_v57]; exact empty_args) hinv48 h64 as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 dropping he_v57 hinv48 e_v57 s48
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__40purify.construct s49 e_v58 (by rw [he_v58]; exact empty_args) hinv49 h64 as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 dropping he_v58 hinv49 e_v58 s49
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s50 e_v59 (by rw [he_v59]; exact empty_args) hinv50 h64 as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 dropping he_v59 hinv50 e_v59 s50
  store_step with Store.apply_rep s51 v59 v8 _ _ hinv51 h64 h_v59 h_v8 (by ns_tac) (by ns_tac) as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 dropping h_v59 hinv51 s51 v59
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s52 0#u32 (0) (by scalar_tac) hinv52 h64 as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 dropping hinv52 s52
  store_step with Store.apply_rep s53 v60 v61 _ _ hinv53 h64 h_v60 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 dropping h_v60 h_v61 hinv53 s53 v60 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s54 e_v63 (by rw [he_v63]; exact empty_args) hinv54 h64 as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 h_v62 dropping he_v63 hinv54 e_v63 s54
  store_step with Store.apply_rep s55 v63 v8 _ _ hinv55 h64 h_v63 h_v8 (by ns_tac) (by ns_tac) as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 h_v62 dropping h_v63 hinv55 s55 v63
  store_step with Store.apply_rep s56 v64 v5 _ _ hinv56 h64 h_v64 h_v5 (by ns_tac) (by ns_tac) as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 h_v62 dropping h_v64 hinv56 s56 v64
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s57 0#u32 (0) (by scalar_tac) hinv57 h64 as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 h_v62 h_v65 dropping hinv57 s57
  store_step with Store.apply_rep s58 v65 v66 _ _ hinv58 h64 h_v65 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 h_v62 dropping h_v65 h_v66 hinv58 s58 v65 v66
  store_step with Store.apply_rep s59 v62 v67 _ _ hinv59 h64 h_v62 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 h_v58 dropping h_v62 h_v67 hinv59 s59 v62 v67
  store_step with Store.apply_rep s60 v58 v68 _ _ hinv60 h64 h_v58 h_v68 (by ns_tac) (by ns_tac) as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v57 dropping h_v58 h_v68 hinv60 s60 v58 v68
  store_step with Store.apply_rep s61 v57 v69 _ _ hinv61 h64 h_v57 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 dropping h_v57 h_v69 hinv61 s61 v57 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s62 e_v71 (by rw [he_v71]; exact empty_args) hinv62 h64 as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 dropping he_v71 hinv62 e_v71 s62
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo__40purify.construct s63 e_v72 (by rw [he_v72]; exact empty_args) hinv63 h64 as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 dropping he_v72 hinv63 e_v72 s63
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s64 e_v73 (by rw [he_v73]; exact empty_args) hinv64 h64 as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 dropping he_v73 hinv64 e_v73 s64
  store_step with Store.apply_rep s65 v73 v8 _ _ hinv65 h64 h_v73 h_v8 (by ns_tac) (by ns_tac) as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 dropping h_v73 hinv65 s65 v73
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s66 e_v75 (by rw [he_v75]; exact empty_args) hinv66 h64 as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v74 dropping he_v75 hinv66 e_v75 s66
  store_step with Store.apply_rep s67 v75 v8 _ _ hinv67 h64 h_v75 h_v8 (by ns_tac) (by ns_tac) as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v74 dropping h_v75 hinv67 s67 v75
  store_step with Store.apply_rep s68 v76 v5 _ _ hinv68 h64 h_v76 h_v5 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v74 dropping h_v76 hinv68 s68 v76
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s69 0#u32 (0) (by scalar_tac) hinv69 h64 as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v74 h_v77 dropping hinv69 s69
  store_step with Store.apply_rep s70 v77 v78 _ _ hinv70 h64 h_v77 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v74 dropping h_v77 h_v78 hinv70 s70 v77 v78
  store_step with Store.apply_rep s71 v74 v79 _ _ hinv71 h64 h_v74 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 dropping h_v74 h_v79 hinv71 s71 v74 v79
  step as ⟨e_v81, he_v81⟩
  store_step with CtorSpec.eo__2d.construct s72 e_v81 (by rw [he_v81]; exact empty_args) hinv72 h64 as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 dropping he_v81 hinv72 e_v81 s72
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s73 e_v82 (by rw [he_v82]; exact empty_args) hinv73 h64 as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v81 dropping he_v82 hinv73 e_v82 s73
  store_step with Store.apply_rep s74 v82 v8 _ _ hinv74 h64 h_v82 h_v8 (by ns_tac) (by ns_tac) as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v81 dropping h_v82 hinv74 s74 v82
  store_step with Store.apply_rep s75 v83 v5 _ _ hinv75 h64 h_v83 h_v5 (by ns_tac) (by ns_tac) as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v81 dropping h_v83 hinv75 s75 v83
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s76 1#u32 (1) (by scalar_tac) hinv76 h64 as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v81 h_v84 dropping hinv76 s76
  store_step with Store.apply_rep s77 v84 v85 _ _ hinv77 h64 h_v84 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v81 dropping h_v84 h_v85 hinv77 s77 v84 v85
  store_step with Store.apply_rep s78 v81 v86 _ _ hinv78 h64 h_v81 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 dropping h_v81 h_v86 hinv78 s78 v81 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s79 e_v88 (by rw [he_v88]; exact empty_args) hinv79 h64 as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v87 dropping he_v88 hinv79 e_v88 s79
  store_step with Store.apply_rep s80 v88 v8 _ _ hinv80 h64 h_v88 h_v8 (by ns_tac) (by ns_tac) as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v87 dropping h_v88 hinv80 s80 v88
  store_step with Store.apply_rep s81 v89 v5 _ _ hinv81 h64 h_v89 h_v5 (by ns_tac) (by ns_tac) as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v87 dropping h_v89 hinv81 s81 v89
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s82 0#u32 (0) (by scalar_tac) hinv82 h64 as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v87 h_v90 dropping hinv82 s82
  store_step with Store.apply_rep s83 v90 v91 _ _ hinv83 h64 h_v90 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 h_v87 dropping h_v90 h_v91 hinv83 s83 v90 v91
  store_step with Store.apply_rep s84 v87 v92 _ _ hinv84 h64 h_v87 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 h_v80 dropping h_v87 h_v92 hinv84 s84 v87 v92
  store_step with Store.apply_rep s85 v80 v93 _ _ hinv85 h64 h_v80 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 h_v72 dropping h_v80 h_v93 hinv85 s85 v80 v93
  store_step with Store.apply_rep s86 v72 v94 _ _ hinv86 h64 h_v72 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v71 dropping h_v72 h_v94 hinv86 s86 v72 v94
  store_step with Store.apply_rep s87 v71 v95 _ _ hinv87 h64 h_v71 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 dropping h_v71 h_v95 hinv87 s87 v71 v95
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s88 e_v97 (by rw [he_v97]; exact empty_args) hinv88 h64 as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 dropping he_v97 hinv88 e_v97 s88
  step as ⟨e_v98, he_v98⟩
  store_step with CtorSpec.eo__40purify.construct s89 e_v98 (by rw [he_v98]; exact empty_args) hinv89 h64 as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 dropping he_v98 hinv89 e_v98 s89
  step as ⟨e_v99, he_v99⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s90 e_v99 (by rw [he_v99]; exact empty_args) hinv90 h64 as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 dropping he_v99 hinv90 e_v99 s90
  store_step with Store.apply_rep s91 v99 v8 _ _ hinv91 h64 h_v99 h_v8 (by ns_tac) (by ns_tac) as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 dropping h_v99 hinv91 s91 v99
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s92 e_v101 (by rw [he_v101]; exact empty_args) hinv92 h64 as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v100 dropping he_v101 hinv92 e_v101 s92
  store_step with Store.apply_rep s93 v101 v8 _ _ hinv93 h64 h_v101 h_v8 (by ns_tac) (by ns_tac) as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v100 dropping h_v101 hinv93 s93 v101
  store_step with Store.apply_rep s94 v102 v5 _ _ hinv94 h64 h_v102 h_v5 (by ns_tac) (by ns_tac) as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v100 dropping h_v102 hinv94 s94 v102
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s95 1#u32 (1) (by scalar_tac) hinv95 h64 as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v100 h_v103 dropping hinv95 s95
  store_step with Store.apply_rep s96 v103 v104 _ _ hinv96 h64 h_v103 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v100 dropping h_v103 h_v104 hinv96 s96 v103 v104
  store_step with Store.apply_rep s97 v100 v105 _ _ hinv97 h64 h_v100 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 dropping h_v100 h_v105 hinv97 s97 v100 v105
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo__2d.construct s98 e_v107 (by rw [he_v107]; exact empty_args) hinv98 h64 as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 dropping he_v107 hinv98 e_v107 s98
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_str_2elen.construct s99 e_v108 (by rw [he_v108]; exact empty_args) hinv99 h64 as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v107 dropping he_v108 hinv99 e_v108 s99
  store_step with Store.apply_rep s100 v108 v8 _ _ hinv100 h64 h_v108 h_v8 (by ns_tac) (by ns_tac) as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v107 dropping h_v108 hinv100 s100 v108
  store_step with Store.apply_rep s101 v107 v109 _ _ hinv101 h64 h_v107 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 dropping h_v107 h_v109 hinv101 s101 v107 v109
  step as ⟨e_v111, he_v111⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s102 e_v111 (by rw [he_v111]; exact empty_args) hinv102 h64 as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v110 dropping he_v111 hinv102 e_v111 s102
  store_step with Store.apply_rep s103 v111 v8 _ _ hinv103 h64 h_v111 h_v8 (by ns_tac) (by ns_tac) as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v110 dropping h_v111 hinv103 s103 v111
  store_step with Store.apply_rep s104 v112 v5 _ _ hinv104 h64 h_v112 h_v5 (by ns_tac) (by ns_tac) as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v110 dropping h_v112 hinv104 s104 v112
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s105 1#u32 (1) (by scalar_tac) hinv105 h64 as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v110 h_v113 dropping hinv105 s105
  store_step with Store.apply_rep s106 v113 v114 _ _ hinv106 h64 h_v113 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 h_v110 dropping h_v113 h_v114 hinv106 s106 v113 v114
  store_step with Store.apply_rep s107 v110 v115 _ _ hinv107 h64 h_v110 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 h_v106 dropping h_v110 h_v115 hinv107 s107 v110 v115
  store_step with Store.apply_rep s108 v106 v116 _ _ hinv108 h64 h_v106 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 h_v98 dropping h_v106 h_v116 hinv108 s108 v106 v116
  store_step with Store.apply_rep s109 v98 v117 _ _ hinv109 h64 h_v98 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v97 dropping h_v117 h_v98 hinv109 s109 v117 v98
  store_step with Store.apply_rep s110 v97 v118 _ _ hinv110 h64 h_v97 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 dropping h_v118 h_v97 hinv110 s110 v118 v97
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s111 _ _ rfl hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 h_v119 dropping hinv111 s111
  store_step with Store.apply_rep s112 v119 v120 _ _ hinv112 h64 h_v119 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 h_v96 dropping h_v119 h_v120 hinv112 s112 v119 v120
  store_step with Store.apply_rep s113 v96 v121 _ _ hinv113 h64 h_v96 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 h_v70 dropping h_v121 h_v96 hinv113 s113 v121 v96
  store_step with Store.apply_rep s114 v70 v122 _ _ hinv114 h64 h_v70 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 h_v56 dropping h_v122 h_v70 hinv114 s114 v122 v70
  store_step with Store.apply_rep s115 v56 v123 _ _ hinv115 h64 h_v56 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v54 dropping h_v123 h_v56 hinv115 s115 v123 v56
  store_step with Store.apply_rep s116 v54 v124 _ _ hinv116 h64 h_v54 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 dropping h_v124 h_v54 hinv116 s116 v124 v54
  step as ⟨e_v126, he_v126⟩
  store_step with CtorSpec.eo_and.construct s117 e_v126 (by rw [he_v126]; exact empty_args) hinv117 h64 as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 dropping he_v126 hinv117 e_v126 s117
  step as ⟨e_v127, he_v127⟩
  store_step with CtorSpec.eo__3d.construct s118 e_v127 (by rw [he_v127]; exact empty_args) hinv118 h64 as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 dropping he_v127 hinv118 e_v127 s118
  step as ⟨e_v128, he_v128⟩
  store_step with CtorSpec.eo_str_2elen.construct s119 e_v128 (by rw [he_v128]; exact empty_args) hinv119 h64 as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 dropping he_v128 hinv119 e_v128 s119
  step as ⟨e_v129, he_v129⟩
  store_step with CtorSpec.eo__40purify.construct s120 e_v129 (by rw [he_v129]; exact empty_args) hinv120 h64 as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 dropping he_v129 hinv120 e_v129 s120
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s121 e_v130 (by rw [he_v130]; exact empty_args) hinv121 h64 as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 dropping he_v130 hinv121 e_v130 s121
  store_step with Store.apply_rep s122 v130 v8 _ _ hinv122 h64 h_v130 h_v8 (by ns_tac) (by ns_tac) as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 dropping h_v130 hinv122 s122 v130
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s123 0#u32 (0) (by scalar_tac) hinv123 h64 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 h_v131 dropping hinv123 s123
  store_step with Store.apply_rep s124 v131 v132 _ _ hinv124 h64 h_v131 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 dropping h_v131 h_v132 hinv124 s124 v131 v132
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s125 e_v134 (by rw [he_v134]; exact empty_args) hinv125 h64 as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 h_v133 dropping he_v134 hinv125 e_v134 s125
  store_step with Store.apply_rep s126 v134 v8 _ _ hinv126 h64 h_v134 h_v8 (by ns_tac) (by ns_tac) as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 h_v133 dropping h_v134 hinv126 s126 v134
  store_step with Store.apply_rep s127 v135 v5 _ _ hinv127 h64 h_v135 h_v5 (by ns_tac) (by ns_tac) as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 h_v133 dropping h_v135 hinv127 s127 v135
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s128 0#u32 (0) (by scalar_tac) hinv128 h64 as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 h_v133 h_v136 dropping hinv128 s128
  store_step with Store.apply_rep s129 v136 v137 _ _ hinv129 h64 h_v136 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 h_v133 dropping h_v136 h_v137 hinv129 s129 v136 v137
  store_step with Store.apply_rep s130 v133 v138 _ _ hinv130 h64 h_v133 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 h_v129 dropping h_v133 h_v138 hinv130 s130 v133 v138
  store_step with Store.apply_rep s131 v129 v139 _ _ hinv131 h64 h_v129 h_v139 (by ns_tac) (by ns_tac) as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 h_v128 dropping h_v129 h_v139 hinv131 s131 v129 v139
  store_step with Store.apply_rep s132 v128 v140 _ _ hinv132 h64 h_v128 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v127 dropping h_v128 h_v140 hinv132 s132 v128 v140
  store_step with Store.apply_rep s133 v127 v141 _ _ hinv133 h64 h_v127 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 dropping h_v127 h_v141 hinv133 s133 v127 v141
  step as ⟨e_v143, he_v143⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s134 e_v143 (by rw [he_v143]; exact empty_args) hinv134 h64 as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v142 dropping he_v143 hinv134 e_v143 s134
  store_step with Store.apply_rep s135 v143 v8 _ _ hinv135 h64 h_v143 h_v8 (by ns_tac) (by ns_tac) as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v142 dropping h_v143 hinv135 s135 v143
  store_step with Store.apply_rep s136 v144 v5 _ _ hinv136 h64 h_v144 h_v5 (by ns_tac) (by ns_tac) as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v142 dropping h_v144 hinv136 s136 v144
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s137 0#u32 (0) (by scalar_tac) hinv137 h64 as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v142 h_v145 dropping hinv137 s137
  store_step with Store.apply_rep s138 v145 v146 _ _ hinv138 h64 h_v145 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 h_v142 dropping h_v145 h_v146 hinv138 s138 v145 v146
  store_step with Store.apply_rep s139 v142 v147 _ _ hinv139 h64 h_v142 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v126 dropping h_v142 h_v147 hinv139 s139 v142 v147
  store_step with Store.apply_rep s140 v126 v148 _ _ hinv140 h64 h_v126 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 dropping h_v126 h_v148 hinv140 s140 v126 v148
  step as ⟨e_v150, he_v150⟩
  store_step with CtorSpec.eo_and.construct s141 e_v150 (by rw [he_v150]; exact empty_args) hinv141 h64 as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 dropping he_v150 hinv141 e_v150 s141
  step as ⟨e_v151, he_v151⟩
  store_step with CtorSpec.eo_forall.construct s142 e_v151 (by rw [he_v151]; exact empty_args) hinv142 h64 as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 dropping he_v151 hinv142 e_v151 s142
  step as ⟨e_v152, he_v152⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s143 e_v152 (by rw [he_v152]; exact empty_args) hinv143 h64 as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 dropping he_v152 hinv143 e_v152 s143
  step as ⟨e_v153, he_v153⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s144 _ _ rfl hinv144 h64 as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 h_v152 dropping hinv144 s144
  replace h_v153 := Represents.rep_of_eq h_v153 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v153]; decide)
  step as ⟨e_v154, he_v154⟩
  store_step with CtorSpec.eo_Int.construct s145 e_v154 (by rw [he_v154]; exact empty_args) hinv145 h64 as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 h_v152 h_v153 dropping he_v153 he_v154 hinv145 e_v153 e_v154 s145
  step as ⟨e_v155, he_v155⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s146 e_v155 (by rw [he_v155]; rfl) h_v153 h_v154 hinv146 h64 as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 h_v152 dropping h_v153 h_v154 he_v155 hinv146 e_v155 s146 v153 v154
  store_step with Store.apply_rep s147 v152 v155 _ _ hinv147 h64 h_v152 h_v155 (by ns_tac) (by ns_tac) as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 dropping h_v152 h_v155 hinv147 s147 v152 v155
  step as ⟨e_v157, he_v157⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s148 e_v157 (by rw [he_v157]; exact empty_args) hinv148 h64 as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 h_v156 dropping he_v157 hinv148 e_v157 s148
  store_step with Store.apply_rep s149 v156 v157 _ _ hinv149 h64 h_v156 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v151 dropping h_v156 h_v157 hinv149 s149 v156 v157
  store_step with Store.apply_rep s150 v151 v158 _ _ hinv150 h64 h_v151 h_v158 (by ns_tac) (by ns_tac) as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 dropping h_v151 h_v158 hinv150 s150 v151 v158
  step as ⟨e_v160, he_v160⟩
  store_step with CtorSpec.eo_or.construct s151 e_v160 (by rw [he_v160]; exact empty_args) hinv151 h64 as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 dropping he_v160 hinv151 e_v160 s151
  step as ⟨e_v161, he_v161⟩
  store_step with CtorSpec.eo_not.construct s152 e_v161 (by rw [he_v161]; exact empty_args) hinv152 h64 as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 dropping he_v161 hinv152 e_v161 s152
  step as ⟨e_v162, he_v162⟩
  store_step with CtorSpec.eo__3e_3d.construct s153 e_v162 (by rw [he_v162]; exact empty_args) hinv153 h64 as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 dropping he_v162 hinv153 e_v162 s153
  step as ⟨e_v163, he_v163⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s154 _ _ rfl hinv154 h64 as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 h_v162 dropping hinv154 s154
  replace h_v163 := Represents.rep_of_eq h_v163 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v163]; decide)
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo_Int.construct s155 e_v164 (by rw [he_v164]; exact empty_args) hinv155 h64 as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 h_v162 h_v163 dropping he_v163 he_v164 hinv155 e_v163 e_v164 s155
  step as ⟨e_v165, he_v165⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s156 e_v165 (by rw [he_v165]; rfl) h_v163 h_v164 hinv156 h64 as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 h_v162 dropping h_v163 h_v164 he_v165 hinv156 e_v165 s156 v163 v164
  store_step with Store.apply_rep s157 v162 v165 _ _ hinv157 h64 h_v162 h_v165 (by ns_tac) (by ns_tac) as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 dropping h_v162 h_v165 hinv157 s157 v162 v165
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s158 0#u32 (0) (by scalar_tac) hinv158 h64 as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 h_v166 dropping hinv158 s158
  store_step with Store.apply_rep s159 v166 v167 _ _ hinv159 h64 h_v166 h_v167 (by ns_tac) (by ns_tac) as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 h_v161 dropping h_v166 h_v167 hinv159 s159 v166 v167
  store_step with Store.apply_rep s160 v161 v168 _ _ hinv160 h64 h_v161 h_v168 (by ns_tac) (by ns_tac) as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v160 dropping h_v161 h_v168 hinv160 s160 v161 v168
  store_step with Store.apply_rep s161 v160 v169 _ _ hinv161 h64 h_v160 h_v169 (by ns_tac) (by ns_tac) as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 dropping h_v160 h_v169 hinv161 s161 v160 v169
  step as ⟨e_v171, he_v171⟩
  store_step with CtorSpec.eo_or.construct s162 e_v171 (by rw [he_v171]; exact empty_args) hinv162 h64 as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 dropping he_v171 hinv162 e_v171 s162
  step as ⟨e_v172, he_v172⟩
  store_step with CtorSpec.eo_not.construct s163 e_v172 (by rw [he_v172]; exact empty_args) hinv163 h64 as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 dropping he_v172 hinv163 e_v172 s163
  step as ⟨e_v173, he_v173⟩
  store_step with CtorSpec.eo__3c.construct s164 e_v173 (by rw [he_v173]; exact empty_args) hinv164 h64 as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 dropping he_v173 hinv164 e_v173 s164
  step as ⟨e_v174, he_v174⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s165 _ _ rfl hinv165 h64 as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v173 dropping hinv165 s165
  replace h_v174 := Represents.rep_of_eq h_v174 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v174]; decide)
  step as ⟨e_v175, he_v175⟩
  store_step with CtorSpec.eo_Int.construct s166 e_v175 (by rw [he_v175]; exact empty_args) hinv166 h64 as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v173 h_v174 dropping he_v174 he_v175 hinv166 e_v174 e_v175 s166
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s167 e_v176 (by rw [he_v176]; rfl) h_v174 h_v175 hinv167 h64 as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v173 dropping h_v174 h_v175 he_v176 hinv167 e_v176 s167 v174 v175
  store_step with Store.apply_rep s168 v173 v176 _ _ hinv168 h64 h_v173 h_v176 (by ns_tac) (by ns_tac) as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 dropping h_v173 h_v176 hinv168 s168 v173 v176
  step as ⟨e_v178, he_v178⟩
  store_step with CtorSpec.eo_str_2elen.construct s169 e_v178 (by rw [he_v178]; exact empty_args) hinv169 h64 as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 dropping he_v178 hinv169 e_v178 s169
  step as ⟨e_v179, he_v179⟩
  store_step with CtorSpec.eo__40purify.construct s170 e_v179 (by rw [he_v179]; exact empty_args) hinv170 h64 as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 dropping he_v179 hinv170 e_v179 s170
  step as ⟨e_v180, he_v180⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s171 e_v180 (by rw [he_v180]; exact empty_args) hinv171 h64 as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 dropping he_v180 hinv171 e_v180 s171
  store_step with Store.apply_rep s172 v180 v8 _ _ hinv172 h64 h_v180 h_v8 (by ns_tac) (by ns_tac) as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v180 hinv172 s172 v180
  step as ⟨e_v182, he_v182⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s173 e_v182 (by rw [he_v182]; exact empty_args) hinv173 h64 as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v181 dropping he_v182 hinv173 e_v182 s173
  store_step with Store.apply_rep s174 v182 v8 _ _ hinv174 h64 h_v182 h_v8 (by ns_tac) (by ns_tac) as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v181 dropping h_v182 hinv174 s174 v182
  store_step with Store.apply_rep s175 v183 v5 _ _ hinv175 h64 h_v183 h_v5 (by ns_tac) (by ns_tac) as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v181 dropping h_v183 hinv175 s175 v183
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s176 0#u32 (0) (by scalar_tac) hinv176 h64 as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v181 h_v184 dropping hinv176 s176
  store_step with Store.apply_rep s177 v184 v185 _ _ hinv177 h64 h_v184 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v181 dropping h_v184 h_v185 hinv177 s177 v184 v185
  store_step with Store.apply_rep s178 v181 v186 _ _ hinv178 h64 h_v181 h_v186 (by ns_tac) (by ns_tac) as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v181 h_v186 hinv178 s178 v181 v186
  step as ⟨e_v188, he_v188⟩
  store_step with CtorSpec.eo__2d.construct s179 e_v188 (by rw [he_v188]; exact empty_args) hinv179 h64 as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 dropping he_v188 hinv179 e_v188 s179
  step as ⟨e_v189, he_v189⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s180 e_v189 (by rw [he_v189]; exact empty_args) hinv180 h64 as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v188 dropping he_v189 hinv180 e_v189 s180
  store_step with Store.apply_rep s181 v189 v8 _ _ hinv181 h64 h_v189 h_v8 (by ns_tac) (by ns_tac) as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v188 dropping h_v189 hinv181 s181 v189
  store_step with Store.apply_rep s182 v190 v5 _ _ hinv182 h64 h_v190 h_v5 (by ns_tac) (by ns_tac) as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v188 dropping h_v190 hinv182 s182 v190
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s183 1#u32 (1) (by scalar_tac) hinv183 h64 as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v188 h_v191 dropping hinv183 s183
  store_step with Store.apply_rep s184 v191 v192 _ _ hinv184 h64 h_v191 h_v192 (by ns_tac) (by ns_tac) as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v188 dropping h_v191 h_v192 hinv184 s184 v191 v192
  store_step with Store.apply_rep s185 v188 v193 _ _ hinv185 h64 h_v188 h_v193 (by ns_tac) (by ns_tac) as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 dropping h_v188 h_v193 hinv185 s185 v188 v193
  step as ⟨e_v195, he_v195⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s186 e_v195 (by rw [he_v195]; exact empty_args) hinv186 h64 as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v194 dropping he_v195 hinv186 e_v195 s186
  store_step with Store.apply_rep s187 v195 v8 _ _ hinv187 h64 h_v195 h_v8 (by ns_tac) (by ns_tac) as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v194 dropping h_v195 hinv187 s187 v195
  store_step with Store.apply_rep s188 v196 v5 _ _ hinv188 h64 h_v196 h_v5 (by ns_tac) (by ns_tac) as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v194 dropping h_v196 hinv188 s188 v196
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s189 0#u32 (0) (by scalar_tac) hinv189 h64 as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v194 h_v197 dropping hinv189 s189
  store_step with Store.apply_rep s190 v197 v198 _ _ hinv190 h64 h_v197 h_v198 (by ns_tac) (by ns_tac) as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 h_v194 dropping h_v197 h_v198 hinv190 s190 v197 v198
  store_step with Store.apply_rep s191 v194 v199 _ _ hinv191 h64 h_v194 h_v199 (by ns_tac) (by ns_tac) as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 h_v187 dropping h_v194 h_v199 hinv191 s191 v194 v199
  store_step with Store.apply_rep s192 v187 v200 _ _ hinv192 h64 h_v187 h_v200 (by ns_tac) (by ns_tac) as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 h_v179 dropping h_v187 h_v200 hinv192 s192 v187 v200
  store_step with Store.apply_rep s193 v179 v201 _ _ hinv193 h64 h_v179 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 h_v178 dropping h_v179 h_v201 hinv193 s193 v179 v201
  store_step with Store.apply_rep s194 v178 v202 _ _ hinv194 h64 h_v178 h_v202 (by ns_tac) (by ns_tac) as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 h_v177 dropping h_v178 h_v202 hinv194 s194 v178 v202
  store_step with Store.apply_rep s195 v177 v203 _ _ hinv195 h64 h_v177 h_v203 (by ns_tac) (by ns_tac) as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 h_v172 dropping h_v177 h_v203 hinv195 s195 v177 v203
  store_step with Store.apply_rep s196 v172 v204 _ _ hinv196 h64 h_v172 h_v204 (by ns_tac) (by ns_tac) as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v171 dropping h_v172 h_v204 hinv196 s196 v172 v204
  store_step with Store.apply_rep s197 v171 v205 _ _ hinv197 h64 h_v171 h_v205 (by ns_tac) (by ns_tac) as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 dropping h_v171 h_v205 hinv197 s197 v171 v205
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo_or.construct s198 e_v207 (by rw [he_v207]; exact empty_args) hinv198 h64 as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 dropping he_v207 hinv198 e_v207 s198
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo_not.construct s199 e_v208 (by rw [he_v208]; exact empty_args) hinv199 h64 as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 dropping he_v208 hinv199 e_v208 s199
  step as ⟨e_v209, he_v209⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s200 e_v209 (by rw [he_v209]; exact empty_args) hinv200 h64 as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 dropping he_v209 hinv200 e_v209 s200
  step as ⟨e_v210, he_v210⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s201 e_v210 (by rw [he_v210]; exact empty_args) hinv201 h64 as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 dropping he_v210 hinv201 e_v210 s201
  step as ⟨e_v211, he_v211⟩
  store_step with CtorSpec.eo__40purify.construct s202 e_v211 (by rw [he_v211]; exact empty_args) hinv202 h64 as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 dropping he_v211 hinv202 e_v211 s202
  step as ⟨e_v212, he_v212⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s203 e_v212 (by rw [he_v212]; exact empty_args) hinv203 h64 as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 dropping he_v212 hinv203 e_v212 s203
  store_step with Store.apply_rep s204 v212 v8 _ _ hinv204 h64 h_v212 h_v8 (by ns_tac) (by ns_tac) as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 dropping h_v212 hinv204 s204 v212
  step as ⟨e_v214, he_v214⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s205 e_v214 (by rw [he_v214]; exact empty_args) hinv205 h64 as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v213 dropping he_v214 hinv205 e_v214 s205
  store_step with Store.apply_rep s206 v214 v8 _ _ hinv206 h64 h_v214 h_v8 (by ns_tac) (by ns_tac) as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v213 dropping h_v214 hinv206 s206 v214
  store_step with Store.apply_rep s207 v215 v5 _ _ hinv207 h64 h_v215 h_v5 (by ns_tac) (by ns_tac) as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v213 dropping h_v215 hinv207 s207 v215
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s208 0#u32 (0) (by scalar_tac) hinv208 h64 as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v213 h_v216 dropping hinv208 s208
  store_step with Store.apply_rep s209 v216 v217 _ _ hinv209 h64 h_v216 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v213 dropping h_v216 h_v217 hinv209 s209 v216 v217
  store_step with Store.apply_rep s210 v213 v218 _ _ hinv210 h64 h_v213 h_v218 (by ns_tac) (by ns_tac) as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 dropping h_v213 h_v218 hinv210 s210 v213 v218
  step as ⟨e_v220, he_v220⟩
  store_step with CtorSpec.eo__2d.construct s211 e_v220 (by rw [he_v220]; exact empty_args) hinv211 h64 as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 dropping he_v220 hinv211 e_v220 s211
  step as ⟨e_v221, he_v221⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s212 e_v221 (by rw [he_v221]; exact empty_args) hinv212 h64 as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v220 dropping he_v221 hinv212 e_v221 s212
  store_step with Store.apply_rep s213 v221 v8 _ _ hinv213 h64 h_v221 h_v8 (by ns_tac) (by ns_tac) as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v220 dropping h_v221 hinv213 s213 v221
  store_step with Store.apply_rep s214 v222 v5 _ _ hinv214 h64 h_v222 h_v5 (by ns_tac) (by ns_tac) as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v220 dropping h_v222 hinv214 s214 v222
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s215 1#u32 (1) (by scalar_tac) hinv215 h64 as ⟨v224, s216, hinv216, h_v224⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v220 h_v223 dropping hinv215 s215
  store_step with Store.apply_rep s216 v223 v224 _ _ hinv216 h64 h_v223 h_v224 (by ns_tac) (by ns_tac) as ⟨v225, s217, hinv217, h_v225⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v220 dropping h_v223 h_v224 hinv216 s216 v223 v224
  store_step with Store.apply_rep s217 v220 v225 _ _ hinv217 h64 h_v220 h_v225 (by ns_tac) (by ns_tac) as ⟨v226, s218, hinv218, h_v226⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 dropping h_v220 h_v225 hinv217 s217 v220 v225
  step as ⟨e_v227, he_v227⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s218 e_v227 (by rw [he_v227]; exact empty_args) hinv218 h64 as ⟨v227, s219, hinv219, h_v227⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v226 dropping he_v227 hinv218 e_v227 s218
  store_step with Store.apply_rep s219 v227 v8 _ _ hinv219 h64 h_v227 h_v8 (by ns_tac) (by ns_tac) as ⟨v228, s220, hinv220, h_v228⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v226 dropping h_v227 hinv219 s219 v227
  store_step with Store.apply_rep s220 v228 v5 _ _ hinv220 h64 h_v228 h_v5 (by ns_tac) (by ns_tac) as ⟨v229, s221, hinv221, h_v229⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v226 dropping h_v228 hinv220 s220 v228
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s221 0#u32 (0) (by scalar_tac) hinv221 h64 as ⟨v230, s222, hinv222, h_v230⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v226 h_v229 dropping hinv221 s221
  store_step with Store.apply_rep s222 v229 v230 _ _ hinv222 h64 h_v229 h_v230 (by ns_tac) (by ns_tac) as ⟨v231, s223, hinv223, h_v231⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 h_v226 dropping h_v229 h_v230 hinv222 s222 v229 v230
  store_step with Store.apply_rep s223 v226 v231 _ _ hinv223 h64 h_v226 h_v231 (by ns_tac) (by ns_tac) as ⟨v232, s224, hinv224, h_v232⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 h_v219 dropping h_v226 h_v231 hinv223 s223 v226 v231
  store_step with Store.apply_rep s224 v219 v232 _ _ hinv224 h64 h_v219 h_v232 (by ns_tac) (by ns_tac) as ⟨v233, s225, hinv225, h_v233⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 h_v211 dropping h_v219 h_v232 hinv224 s224 v219 v232
  store_step with Store.apply_rep s225 v211 v233 _ _ hinv225 h64 h_v211 h_v233 (by ns_tac) (by ns_tac) as ⟨v234, s226, hinv226, h_v234⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v210 dropping h_v211 h_v233 hinv225 s225 v211 v233
  store_step with Store.apply_rep s226 v210 v234 _ _ hinv226 h64 h_v210 h_v234 (by ns_tac) (by ns_tac) as ⟨v235, s227, hinv227, h_v235⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 dropping h_v210 h_v234 hinv226 s226 v210 v234
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s227 0#u32 (0) (by scalar_tac) hinv227 h64 as ⟨v236, s228, hinv228, h_v236⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v235 dropping hinv227 s227
  store_step with Store.apply_rep s228 v235 v236 _ _ hinv228 h64 h_v235 h_v236 (by ns_tac) (by ns_tac) as ⟨v237, s229, hinv229, h_v237⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 dropping h_v235 h_v236 hinv228 s228 v235 v236
  step as ⟨e_v238, he_v238⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s229 _ _ rfl hinv229 h64 as ⟨v238, s230, hinv230, h_v238⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v237 dropping hinv229 s229
  replace h_v238 := Represents.rep_of_eq h_v238 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v238]; decide)
  step as ⟨e_v239, he_v239⟩
  store_step with CtorSpec.eo_Int.construct s230 e_v239 (by rw [he_v239]; exact empty_args) hinv230 h64 as ⟨v239, s231, hinv231, h_v239⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v237 h_v238 dropping he_v238 he_v239 hinv230 e_v238 e_v239 s230
  step as ⟨e_v240, he_v240⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s231 e_v240 (by rw [he_v240]; rfl) h_v238 h_v239 hinv231 h64 as ⟨v240, s232, hinv232, h_v240⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 h_v237 dropping h_v238 h_v239 he_v240 hinv231 e_v240 s231 v238 v239
  store_step with Store.apply_rep s232 v237 v240 _ _ hinv232 h64 h_v237 h_v240 (by ns_tac) (by ns_tac) as ⟨v241, s233, hinv233, h_v241⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 h_v209 dropping h_v237 h_v240 hinv232 s232 v237 v240
  store_step with Store.apply_rep s233 v209 v241 _ _ hinv233 h64 h_v209 h_v241 (by ns_tac) (by ns_tac) as ⟨v242, s234, hinv234, h_v242⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 dropping h_v209 h_v241 hinv233 s233 v209 v241
  store_step with Store.apply_rep s234 v242 v5 _ _ hinv234 h64 h_v242 h_v5 (by ns_tac) (by ns_tac) as ⟨v243, s235, hinv235, h_v243⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 h_v208 dropping h_v242 hinv234 s234 v242
  store_step with Store.apply_rep s235 v208 v243 _ _ hinv235 h64 h_v208 h_v243 (by ns_tac) (by ns_tac) as ⟨v244, s236, hinv236, h_v244⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v207 dropping h_v208 h_v243 hinv235 s235 v208 v243
  store_step with Store.apply_rep s236 v207 v244 _ _ hinv236 h64 h_v207 h_v244 (by ns_tac) (by ns_tac) as ⟨v245, s237, hinv237, h_v245⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 dropping h_v207 h_v244 hinv236 s236 v207 v244
  store_step with Store.literal_boolean_spec s237 false hinv237 h64 as ⟨v246, s238, hinv238, h_v246⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 h_v245 dropping hinv237 s237
  store_step with Store.apply_rep s238 v245 v246 _ _ hinv238 h64 h_v245 h_v246 (by ns_tac) (by ns_tac) as ⟨v247, s239, hinv239, h_v247⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 h_v206 dropping h_v245 h_v246 hinv238 s238 v245 v246
  store_step with Store.apply_rep s239 v206 v247 _ _ hinv239 h64 h_v206 h_v247 (by ns_tac) (by ns_tac) as ⟨v248, s240, hinv240, h_v248⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 h_v170 dropping h_v206 h_v247 hinv239 s239 v206 v247
  store_step with Store.apply_rep s240 v170 v248 _ _ hinv240 h64 h_v170 h_v248 (by ns_tac) (by ns_tac) as ⟨v249, s241, hinv241, h_v249⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 h_v159 dropping h_v170 h_v248 hinv240 s240 v170 v248
  store_step with Store.apply_rep s241 v159 v249 _ _ hinv241 h64 h_v159 h_v249 (by ns_tac) (by ns_tac) as ⟨v250, s242, hinv242, h_v250⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v150 dropping h_v159 h_v249 hinv241 s241 v159 v249
  store_step with Store.apply_rep s242 v150 v250 _ _ hinv242 h64 h_v150 h_v250 (by ns_tac) (by ns_tac) as ⟨v251, s243, hinv243, h_v251⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 dropping h_v150 h_v250 hinv242 s242 v150 v250
  step as ⟨e_v252, he_v252⟩
  store_step with CtorSpec.eo_and.construct s243 e_v252 (by rw [he_v252]; exact empty_args) hinv243 h64 as ⟨v252, s244, hinv244, h_v252⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 dropping he_v252 hinv243 e_v252 s243
  step as ⟨e_v253, he_v253⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s244 e_v253 (by rw [he_v253]; exact empty_args) hinv244 h64 as ⟨v253, s245, hinv245, h_v253⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 dropping he_v253 hinv244 e_v253 s244
  step as ⟨e_v254, he_v254⟩
  store_step with CtorSpec.eo__40purify.construct s245 e_v254 (by rw [he_v254]; exact empty_args) hinv245 h64 as ⟨v254, s246, hinv246, h_v254⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 dropping he_v254 hinv245 e_v254 s245
  step as ⟨e_v255, he_v255⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s246 e_v255 (by rw [he_v255]; exact empty_args) hinv246 h64 as ⟨v255, s247, hinv247, h_v255⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 dropping he_v255 hinv246 e_v255 s246
  store_step with Store.apply_rep s247 v255 v8 _ _ hinv247 h64 h_v255 h_v8 (by ns_tac) (by ns_tac) as ⟨v256, s248, hinv248, h_v256⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 dropping h_v255 hinv247 s247 v255
  step as ⟨e_v257, he_v257⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s248 e_v257 (by rw [he_v257]; exact empty_args) hinv248 h64 as ⟨v257, s249, hinv249, h_v257⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v256 dropping he_v257 hinv248 e_v257 s248
  store_step with Store.apply_rep s249 v257 v8 _ _ hinv249 h64 h_v257 h_v8 (by ns_tac) (by ns_tac) as ⟨v258, s250, hinv250, h_v258⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v256 dropping h_v257 hinv249 s249 v257
  store_step with Store.apply_rep s250 v258 v5 _ _ hinv250 h64 h_v258 h_v5 (by ns_tac) (by ns_tac) as ⟨v259, s251, hinv251, h_v259⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v256 dropping h_v258 hinv250 s250 v258
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s251 0#u32 (0) (by scalar_tac) hinv251 h64 as ⟨v260, s252, hinv252, h_v260⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v256 h_v259 dropping hinv251 s251
  store_step with Store.apply_rep s252 v259 v260 _ _ hinv252 h64 h_v259 h_v260 (by ns_tac) (by ns_tac) as ⟨v261, s253, hinv253, h_v261⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v256 dropping h_v259 h_v260 hinv252 s252 v259 v260
  store_step with Store.apply_rep s253 v256 v261 _ _ hinv253 h64 h_v256 h_v261 (by ns_tac) (by ns_tac) as ⟨v262, s254, hinv254, h_v262⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 dropping h_v256 h_v261 hinv253 s253 v256 v261
  step as ⟨e_v263, he_v263⟩
  store_step with CtorSpec.eo__2d.construct s254 e_v263 (by rw [he_v263]; exact empty_args) hinv254 h64 as ⟨v263, s255, hinv255, h_v263⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 dropping he_v263 hinv254 e_v263 s254
  step as ⟨e_v264, he_v264⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s255 e_v264 (by rw [he_v264]; exact empty_args) hinv255 h64 as ⟨v264, s256, hinv256, h_v264⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v263 dropping he_v264 hinv255 e_v264 s255
  store_step with Store.apply_rep s256 v264 v8 _ _ hinv256 h64 h_v264 h_v8 (by ns_tac) (by ns_tac) as ⟨v265, s257, hinv257, h_v265⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v263 dropping h_v264 hinv256 s256 v264
  store_step with Store.apply_rep s257 v265 v5 _ _ hinv257 h64 h_v265 h_v5 (by ns_tac) (by ns_tac) as ⟨v266, s258, hinv258, h_v266⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v263 dropping h_v265 hinv257 s257 v265
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s258 1#u32 (1) (by scalar_tac) hinv258 h64 as ⟨v267, s259, hinv259, h_v267⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v263 h_v266 dropping hinv258 s258
  store_step with Store.apply_rep s259 v266 v267 _ _ hinv259 h64 h_v266 h_v267 (by ns_tac) (by ns_tac) as ⟨v268, s260, hinv260, h_v268⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v263 dropping h_v266 h_v267 hinv259 s259 v266 v267
  store_step with Store.apply_rep s260 v263 v268 _ _ hinv260 h64 h_v263 h_v268 (by ns_tac) (by ns_tac) as ⟨v269, s261, hinv261, h_v269⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 dropping h_v263 h_v268 hinv260 s260 v263 v268
  step as ⟨e_v270, he_v270⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s261 e_v270 (by rw [he_v270]; exact empty_args) hinv261 h64 as ⟨v270, s262, hinv262, h_v270⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v269 dropping he_v270 hinv261 e_v270 s261
  store_step with Store.apply_rep s262 v270 v8 _ _ hinv262 h64 h_v270 h_v8 (by ns_tac) (by ns_tac) as ⟨v271, s263, hinv263, h_v271⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v269 dropping h_v270 hinv262 s262 v270
  store_step with Store.apply_rep s263 v271 v5 _ _ hinv263 h64 h_v271 h_v5 (by ns_tac) (by ns_tac) as ⟨v272, s264, hinv264, h_v272⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v269 dropping h_v271 hinv263 s263 v271
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s264 0#u32 (0) (by scalar_tac) hinv264 h64 as ⟨v273, s265, hinv265, h_v273⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v269 h_v272 dropping hinv264 s264
  store_step with Store.apply_rep s265 v272 v273 _ _ hinv265 h64 h_v272 h_v273 (by ns_tac) (by ns_tac) as ⟨v274, s266, hinv266, h_v274⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 h_v269 dropping h_v272 h_v273 hinv265 s265 v272 v273
  store_step with Store.apply_rep s266 v269 v274 _ _ hinv266 h64 h_v269 h_v274 (by ns_tac) (by ns_tac) as ⟨v275, s267, hinv267, h_v275⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 h_v262 dropping h_v269 h_v274 hinv266 s266 v269 v274
  store_step with Store.apply_rep s267 v262 v275 _ _ hinv267 h64 h_v262 h_v275 (by ns_tac) (by ns_tac) as ⟨v276, s268, hinv268, h_v276⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 h_v254 dropping h_v262 h_v275 hinv267 s267 v262 v275
  store_step with Store.apply_rep s268 v254 v276 _ _ hinv268 h64 h_v254 h_v276 (by ns_tac) (by ns_tac) as ⟨v277, s269, hinv269, h_v277⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 h_v253 dropping h_v254 h_v276 hinv268 s268 v254 v276
  store_step with Store.apply_rep s269 v253 v277 _ _ hinv269 h64 h_v253 h_v277 (by ns_tac) (by ns_tac) as ⟨v278, s270, hinv270, h_v278⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 dropping h_v253 h_v277 hinv269 s269 v253 v277
  store_step with Store.apply_rep s270 v278 v5 _ _ hinv270 h64 h_v278 h_v5 (by ns_tac) (by ns_tac) as ⟨v279, s271, hinv271, h_v279⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v252 dropping h_v278 hinv270 s270 v278
  store_step with Store.apply_rep s271 v252 v279 _ _ hinv271 h64 h_v252 h_v279 (by ns_tac) (by ns_tac) as ⟨v280, s272, hinv272, h_v280⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 dropping h_v252 h_v279 hinv271 s271 v252 v279
  step as ⟨e_v281, he_v281⟩
  store_step with CtorSpec.eo_and.construct s272 e_v281 (by rw [he_v281]; exact empty_args) hinv272 h64 as ⟨v281, s273, hinv273, h_v281⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 dropping he_v281 hinv272 e_v281 s272
  step as ⟨e_v282, he_v282⟩
  store_step with CtorSpec.eo__3d.construct s273 e_v282 (by rw [he_v282]; exact empty_args) hinv273 h64 as ⟨v282, s274, hinv274, h_v282⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 dropping he_v282 hinv273 e_v282 s273
  step as ⟨e_v283, he_v283⟩
  store_step with CtorSpec.eo__40purify.construct s274 e_v283 (by rw [he_v283]; exact empty_args) hinv274 h64 as ⟨v283, s275, hinv275, h_v283⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v282 dropping he_v283 hinv274 e_v283 s274
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s275 e_v284 (by rw [he_v284]; exact empty_args) hinv275 h64 as ⟨v284, s276, hinv276, h_v284⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v282 h_v283 dropping he_v284 hinv275 e_v284 s275
  store_step with Store.apply_rep s276 v284 v8 _ _ hinv276 h64 h_v284 h_v8 (by ns_tac) (by ns_tac) as ⟨v285, s277, hinv277, h_v285⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v282 h_v283 dropping h_v284 hinv276 s276 v284
  store_step with Store.apply_rep s277 v285 v5 _ _ hinv277 h64 h_v285 h_v5 (by ns_tac) (by ns_tac) as ⟨v286, s278, hinv278, h_v286⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v282 h_v283 dropping h_v285 hinv277 s277 v285
  store_step with Store.apply_rep s278 v286 v2 _ _ hinv278 h64 h_v286 h_v2 (by ns_tac) (by ns_tac) as ⟨v287, s279, hinv279, h_v287⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v282 h_v283 dropping h_v286 hinv278 s278 v286
  store_step with Store.apply_rep s279 v283 v287 _ _ hinv279 h64 h_v283 h_v287 (by ns_tac) (by ns_tac) as ⟨v288, s280, hinv280, h_v288⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v282 dropping h_v283 h_v287 hinv279 s279 v283 v287
  store_step with Store.apply_rep s280 v282 v288 _ _ hinv280 h64 h_v282 h_v288 (by ns_tac) (by ns_tac) as ⟨v289, s281, hinv281, h_v289⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 dropping h_v282 h_v288 hinv280 s280 v282 v288
  step as ⟨e_v290, he_v290⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s281 e_v290 (by rw [he_v290]; exact empty_args) hinv281 h64 as ⟨v290, s282, hinv282, h_v290⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 dropping he_v290 hinv281 e_v290 s281
  step as ⟨e_v291, he_v291⟩
  store_step with CtorSpec.eo__40purify.construct s282 e_v291 (by rw [he_v291]; exact empty_args) hinv282 h64 as ⟨v291, s283, hinv283, h_v291⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 dropping he_v291 hinv282 e_v291 s282
  step as ⟨e_v292, he_v292⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s283 e_v292 (by rw [he_v292]; exact empty_args) hinv283 h64 as ⟨v292, s284, hinv284, h_v292⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 dropping he_v292 hinv283 e_v292 s283
  store_step with Store.apply_rep s284 v292 v8 _ _ hinv284 h64 h_v292 h_v8 (by ns_tac) (by ns_tac) as ⟨v293, s285, hinv285, h_v293⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 dropping h_v292 hinv284 s284 v292
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s285 0#u32 (0) (by scalar_tac) hinv285 h64 as ⟨v294, s286, hinv286, h_v294⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 h_v293 dropping hinv285 s285
  store_step with Store.apply_rep s286 v293 v294 _ _ hinv286 h64 h_v293 h_v294 (by ns_tac) (by ns_tac) as ⟨v295, s287, hinv287, h_v295⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 dropping h_v293 h_v294 hinv286 s286 v293 v294
  step as ⟨e_v296, he_v296⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s287 e_v296 (by rw [he_v296]; exact empty_args) hinv287 h64 as ⟨v296, s288, hinv288, h_v296⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 h_v295 dropping he_v296 hinv287 e_v296 s287
  store_step with Store.apply_rep s288 v296 v8 _ _ hinv288 h64 h_v296 h_v8 (by ns_tac) (by ns_tac) as ⟨v297, s289, hinv289, h_v297⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 h_v295 dropping h_v296 hinv288 s288 v296
  store_step with Store.apply_rep s289 v297 v5 _ _ hinv289 h64 h_v297 h_v5 (by ns_tac) (by ns_tac) as ⟨v298, s290, hinv290, h_v298⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 h_v295 dropping h_v297 hinv289 s289 v297
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s290 0#u32 (0) (by scalar_tac) hinv290 h64 as ⟨v299, s291, hinv291, h_v299⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 h_v295 h_v298 dropping hinv290 s290
  store_step with Store.apply_rep s291 v298 v299 _ _ hinv291 h64 h_v298 h_v299 (by ns_tac) (by ns_tac) as ⟨v300, s292, hinv292, h_v300⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 h_v295 dropping h_v298 h_v299 hinv291 s291 v298 v299
  store_step with Store.apply_rep s292 v295 v300 _ _ hinv292 h64 h_v295 h_v300 (by ns_tac) (by ns_tac) as ⟨v301, s293, hinv293, h_v301⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 h_v291 dropping h_v295 h_v300 hinv292 s292 v295 v300
  store_step with Store.apply_rep s293 v291 v301 _ _ hinv293 h64 h_v291 h_v301 (by ns_tac) (by ns_tac) as ⟨v302, s294, hinv294, h_v302⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v290 dropping h_v291 h_v301 hinv293 s293 v291 v301
  store_step with Store.apply_rep s294 v290 v302 _ _ hinv294 h64 h_v290 h_v302 (by ns_tac) (by ns_tac) as ⟨v303, s295, hinv295, h_v303⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 dropping h_v290 h_v302 hinv294 s294 v290 v302
  step as ⟨e_v304, he_v304⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s295 e_v304 (by rw [he_v304]; exact empty_args) hinv295 h64 as ⟨v304, s296, hinv296, h_v304⟩ growing hG carrying h_v2 h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 dropping he_v304 hinv295 e_v304 s295
  store_step with Store.apply_rep s296 v304 v2 _ _ hinv296 h64 h_v304 h_v2 (by ns_tac) (by ns_tac) as ⟨v305, s297, hinv297, h_v305⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 dropping h_v2 h_v304 hinv296 s296 v2 v304
  step as ⟨e_v306, he_v306⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s297 e_v306 (by rw [he_v306]; exact empty_args) hinv297 h64 as ⟨v306, s298, hinv298, h_v306⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 dropping he_v306 hinv297 e_v306 s297
  step as ⟨e_v307, he_v307⟩
  store_step with CtorSpec.eo__40purify.construct s298 e_v307 (by rw [he_v307]; exact empty_args) hinv298 h64 as ⟨v307, s299, hinv299, h_v307⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 dropping he_v307 hinv298 e_v307 s298
  step as ⟨e_v308, he_v308⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s299 e_v308 (by rw [he_v308]; exact empty_args) hinv299 h64 as ⟨v308, s300, hinv300, h_v308⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 dropping he_v308 hinv299 e_v308 s299
  store_step with Store.apply_rep s300 v308 v8 _ _ hinv300 h64 h_v308 h_v8 (by ns_tac) (by ns_tac) as ⟨v309, s301, hinv301, h_v309⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 dropping h_v308 hinv300 s300 v308
  step as ⟨e_v310, he_v310⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s301 e_v310 (by rw [he_v310]; exact empty_args) hinv301 h64 as ⟨v310, s302, hinv302, h_v310⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v309 dropping he_v310 hinv301 e_v310 s301
  store_step with Store.apply_rep s302 v310 v8 _ _ hinv302 h64 h_v310 h_v8 (by ns_tac) (by ns_tac) as ⟨v311, s303, hinv303, h_v311⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v309 dropping h_v310 hinv302 s302 v310
  store_step with Store.apply_rep s303 v311 v5 _ _ hinv303 h64 h_v311 h_v5 (by ns_tac) (by ns_tac) as ⟨v312, s304, hinv304, h_v312⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v309 dropping h_v311 hinv303 s303 v311
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s304 1#u32 (1) (by scalar_tac) hinv304 h64 as ⟨v313, s305, hinv305, h_v313⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v309 h_v312 dropping hinv304 s304
  store_step with Store.apply_rep s305 v312 v313 _ _ hinv305 h64 h_v312 h_v313 (by ns_tac) (by ns_tac) as ⟨v314, s306, hinv306, h_v314⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v309 dropping h_v312 h_v313 hinv305 s305 v312 v313
  store_step with Store.apply_rep s306 v309 v314 _ _ hinv306 h64 h_v309 h_v314 (by ns_tac) (by ns_tac) as ⟨v315, s307, hinv307, h_v315⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 dropping h_v309 h_v314 hinv306 s306 v309 v314
  step as ⟨e_v316, he_v316⟩
  store_step with CtorSpec.eo__2d.construct s307 e_v316 (by rw [he_v316]; exact empty_args) hinv307 h64 as ⟨v316, s308, hinv308, h_v316⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 dropping he_v316 hinv307 e_v316 s307
  step as ⟨e_v317, he_v317⟩
  store_step with CtorSpec.eo_str_2elen.construct s308 e_v317 (by rw [he_v317]; exact empty_args) hinv308 h64 as ⟨v317, s309, hinv309, h_v317⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v316 dropping he_v317 hinv308 e_v317 s308
  store_step with Store.apply_rep s309 v317 v8 _ _ hinv309 h64 h_v317 h_v8 (by ns_tac) (by ns_tac) as ⟨v318, s310, hinv310, h_v318⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v316 dropping h_v317 hinv309 s309 v317
  store_step with Store.apply_rep s310 v316 v318 _ _ hinv310 h64 h_v316 h_v318 (by ns_tac) (by ns_tac) as ⟨v319, s311, hinv311, h_v319⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 dropping h_v316 h_v318 hinv310 s310 v316 v318
  step as ⟨e_v320, he_v320⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s311 e_v320 (by rw [he_v320]; exact empty_args) hinv311 h64 as ⟨v320, s312, hinv312, h_v320⟩ growing hG carrying h_v5 h_v8 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v319 dropping he_v320 hinv311 e_v320 s311
  store_step with Store.apply_rep s312 v320 v8 _ _ hinv312 h64 h_v320 h_v8 (by ns_tac) (by ns_tac) as ⟨v321, s313, hinv313, h_v321⟩ growing hG carrying h_v5 h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v319 dropping h_v320 h_v8 hinv312 s312 v320 v8
  store_step with Store.apply_rep s313 v321 v5 _ _ hinv313 h64 h_v321 h_v5 (by ns_tac) (by ns_tac) as ⟨v322, s314, hinv314, h_v322⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v319 dropping h_v321 h_v5 hinv313 s313 v321 v5
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s314 1#u32 (1) (by scalar_tac) hinv314 h64 as ⟨v323, s315, hinv315, h_v323⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v319 h_v322 dropping hinv314 s314
  store_step with Store.apply_rep s315 v322 v323 _ _ hinv315 h64 h_v322 h_v323 (by ns_tac) (by ns_tac) as ⟨v324, s316, hinv316, h_v324⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 h_v319 dropping h_v322 h_v323 hinv315 s315 v322 v323
  store_step with Store.apply_rep s316 v319 v324 _ _ hinv316 h64 h_v319 h_v324 (by ns_tac) (by ns_tac) as ⟨v325, s317, hinv317, h_v325⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 h_v315 dropping h_v319 h_v324 hinv316 s316 v319 v324
  store_step with Store.apply_rep s317 v315 v325 _ _ hinv317 h64 h_v315 h_v325 (by ns_tac) (by ns_tac) as ⟨v326, s318, hinv318, h_v326⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 h_v307 dropping h_v315 h_v325 hinv317 s317 v315 v325
  store_step with Store.apply_rep s318 v307 v326 _ _ hinv318 h64 h_v307 h_v326 (by ns_tac) (by ns_tac) as ⟨v327, s319, hinv319, h_v327⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v306 dropping h_v307 h_v326 hinv318 s318 v307 v326
  store_step with Store.apply_rep s319 v306 v327 _ _ hinv319 h64 h_v306 h_v327 (by ns_tac) (by ns_tac) as ⟨v328, s320, hinv320, h_v328⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 dropping h_v306 h_v327 hinv319 s319 v306 v327
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s320 _ _ rfl hinv320 h64 as ⟨v329, s321, hinv321, h_v329⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 h_v328 dropping hinv320 s320
  store_step with Store.apply_rep s321 v328 v329 _ _ hinv321 h64 h_v328 h_v329 (by ns_tac) (by ns_tac) as ⟨v330, s322, hinv322, h_v330⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 h_v305 dropping h_v328 h_v329 hinv321 s321 v328 v329
  store_step with Store.apply_rep s322 v305 v330 _ _ hinv322 h64 h_v305 h_v330 (by ns_tac) (by ns_tac) as ⟨v331, s323, hinv323, h_v331⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 h_v303 dropping h_v305 h_v330 hinv322 s322 v305 v330
  store_step with Store.apply_rep s323 v303 v331 _ _ hinv323 h64 h_v303 h_v331 (by ns_tac) (by ns_tac) as ⟨v332, s324, hinv324, h_v332⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 h_v289 dropping h_v303 h_v331 hinv323 s323 v303 v331
  store_step with Store.apply_rep s324 v289 v332 _ _ hinv324 h64 h_v289 h_v332 (by ns_tac) (by ns_tac) as ⟨v333, s325, hinv325, h_v333⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v281 dropping h_v289 h_v332 hinv324 s324 v289 v332
  store_step with Store.apply_rep s325 v281 v333 _ _ hinv325 h64 h_v281 h_v333 (by ns_tac) (by ns_tac) as ⟨v334, s326, hinv326, h_v334⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 dropping h_v281 h_v333 hinv325 s325 v281 v333
  store_step with Store.literal_boolean_spec s326 true hinv326 h64 as ⟨v335, s327, hinv327, h_v335⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 h_v334 dropping hinv326 s326
  store_step with Store.apply_rep s327 v334 v335 _ _ hinv327 h64 h_v334 h_v335 (by ns_tac) (by ns_tac) as ⟨v336, s328, hinv328, h_v336⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 h_v280 dropping h_v334 h_v335 hinv327 s327 v334 v335
  store_step with Store.apply_rep s328 v280 v336 _ _ hinv328 h64 h_v280 h_v336 (by ns_tac) (by ns_tac) as ⟨v337, s329, hinv329, h_v337⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 h_v251 dropping h_v280 h_v336 hinv328 s328 v280 v336
  store_step with Store.apply_rep s329 v251 v337 _ _ hinv329 h64 h_v251 h_v337 (by ns_tac) (by ns_tac) as ⟨v338, s330, hinv330, h_v338⟩ growing hG carrying h_v32 h_v53 h_v125 h_v149 dropping h_v251 h_v337 hinv329 s329 v251 v337
  store_step with Store.apply_rep s330 v149 v338 _ _ hinv330 h64 h_v149 h_v338 (by ns_tac) (by ns_tac) as ⟨v339, s331, hinv331, h_v339⟩ growing hG carrying h_v32 h_v53 h_v125 dropping h_v149 h_v338 hinv330 s330 v149 v338
  store_step with Store.apply_rep s331 v125 v339 _ _ hinv331 h64 h_v125 h_v339 (by ns_tac) (by ns_tac) as ⟨v340, s332, hinv332, h_v340⟩ growing hG carrying h_v32 h_v53 dropping h_v125 h_v339 hinv331 s331 v125 v339
  store_step with Store.apply_rep s332 v53 v340 _ _ hinv332 h64 h_v53 h_v340 (by ns_tac) (by ns_tac) as ⟨v341, s333, hinv333, h_v341⟩ growing hG carrying h_v32 dropping h_v340 h_v53 hinv332 s332 v340 v53
  store_step with Store.apply_rep s333 v32 v341 _ _ hinv333 h64 h_v32 h_v341 (by ns_tac) (by ns_tac) as ⟨v342, s334, hinv334, h_v342⟩ growing hG carrying dropping h_v32 h_v341 hinv333 s333 v32 v341
  case_done hinv334 hG with h_v342 in EoCases.__str_reduction_pred.case_9 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

set_option maxHeartbeats 13920000 in
theorem case_10_eo__24str_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_10_eo__24str_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__str_reduction_pred.case_10 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__str_reduction_pred.case_10 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24str_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_10
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_10
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv else hinv hG in EoCases.__str_reduction_pred.case_10
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre_5fall.construct s e_v9 (by rw [he_v9]; exact empty_args) hinv h64 as ⟨v9, s1, hinv1, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_a0 h_v1 h_v4 he_v9 e_v9 v1 v4
  pat_same v7 v9 with h_v7 h_v9 using hinv1 else hinv1 hG in EoCases.__str_reduction_pred.case_10
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ite.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v7 h_v9 he_v10 hinv1 e_v10 s1 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping he_v11 hinv2 e_v11 s2
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s3 e_v12 (by rw [he_v12]; exact empty_args) hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping he_v12 hinv3 e_v12 s3
  store_step with Store.apply_rep s4 v12 v8 _ _ hinv4 h64 h_v12 h_v8 (by ns_tac) (by ns_tac) as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v12 hinv4 s4 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_re_2ediff.construct s5 e_v14 (by rw [he_v14]; exact empty_args) hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 dropping he_v14 hinv5 e_v14 s5
  store_step with Store.apply_rep s6 v14 v5 _ _ hinv6 h64 h_v14 h_v5 (by ns_tac) (by ns_tac) as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 dropping h_v14 hinv6 s6 v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 h_v15 dropping he_v16 hinv7 e_v16 s7
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s8 _ _ rfl hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 h_v15 h_v16 dropping hinv8 s8
  store_step with Store.apply_rep s9 v16 v17 _ _ hinv9 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 h_v15 dropping h_v16 h_v17 hinv9 s9 v16 v17
  store_step with Store.apply_rep s10 v15 v18 _ _ hinv10 h64 h_v15 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v13 dropping h_v15 h_v18 hinv10 s10 v15 v18
  store_step with Store.apply_rep s11 v13 v19 _ _ hinv11 h64 h_v13 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v13 h_v19 hinv11 s11 v13 v19
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 h_v20 dropping hinv12 s12
  store_step with Store.apply_rep s13 v20 v21 _ _ hinv13 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v11 dropping h_v20 h_v21 hinv13 s13 v20 v21
  store_step with Store.apply_rep s14 v11 v22 _ _ hinv14 h64 h_v11 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v11 h_v22 hinv14 s14 v11 v22
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s15 1#u32 (-1) (by scalar_tac) hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 h_v23 dropping hinv15 s15
  store_step with Store.apply_rep s16 v23 v24 _ _ hinv16 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_v2 h_v5 h_v8 h_v10 dropping h_v23 h_v24 hinv16 s16 v23 v24
  store_step with Store.apply_rep s17 v10 v25 _ _ hinv17 h64 h_v10 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v10 h_v25 hinv17 s17 v10 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s18 e_v27 (by rw [he_v27]; exact empty_args) hinv18 h64 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 dropping he_v27 hinv18 e_v27 s18
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__40purify.construct s19 e_v28 (by rw [he_v28]; exact empty_args) hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 dropping he_v28 hinv19 e_v28 s19
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre_5fall.construct s20 e_v29 (by rw [he_v29]; exact empty_args) hinv20 h64 as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping he_v29 hinv20 e_v29 s20
  store_step with Store.apply_rep s21 v29 v8 _ _ hinv21 h64 h_v29 h_v8 (by ns_tac) (by ns_tac) as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping h_v29 hinv21 s21 v29
  store_step with Store.apply_rep s22 v30 v5 _ _ hinv22 h64 h_v30 h_v5 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping h_v30 hinv22 s22 v30
  store_step with Store.apply_rep s23 v31 v2 _ _ hinv23 h64 h_v31 h_v2 (by ns_tac) (by ns_tac) as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 h_v28 dropping h_v31 hinv23 s23 v31
  store_step with Store.apply_rep s24 v28 v32 _ _ hinv24 h64 h_v28 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 h_v27 dropping h_v28 h_v32 hinv24 s24 v28 v32
  store_step with Store.apply_rep s25 v27 v33 _ _ hinv25 h64 h_v27 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 dropping h_v27 h_v33 hinv25 s25 v27 v33
  store_step with Store.apply_rep s26 v34 v8 _ _ hinv26 h64 h_v34 h_v8 (by ns_tac) (by ns_tac) as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v8 h_v26 dropping h_v34 hinv26 s26 v34
  store_step with Store.apply_rep s27 v26 v35 _ _ hinv27 h64 h_v26 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v8 dropping h_v26 h_v35 hinv27 s27 v26 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_and.construct s28 e_v37 (by rw [he_v37]; exact empty_args) hinv28 h64 as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 dropping he_v37 hinv28 e_v37 s28
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3e.construct s29 e_v38 (by rw [he_v38]; exact empty_args) hinv29 h64 as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 dropping he_v38 hinv29 e_v38 s29
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s30 e_v39 (by rw [he_v39]; exact empty_args) hinv30 h64 as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 h_v38 dropping he_v39 hinv30 e_v39 s30
  store_step with Store.apply_rep s31 v39 v8 _ _ hinv31 h64 h_v39 h_v8 (by ns_tac) (by ns_tac) as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 h_v38 dropping h_v39 hinv31 s31 v39
  store_step with Store.apply_rep s32 v40 v5 _ _ hinv32 h64 h_v40 h_v5 (by ns_tac) (by ns_tac) as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 h_v38 dropping h_v40 hinv32 s32 v40
  store_step with Store.apply_rep s33 v38 v41 _ _ hinv33 h64 h_v38 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 dropping h_v38 h_v41 hinv33 s33 v38 v41
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s34 0#u32 (0) (by scalar_tac) hinv34 h64 as ⟨v43, s35, hinv35, h_v43⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 h_v42 dropping hinv34 s34
  store_step with Store.apply_rep s35 v42 v43 _ _ hinv35 h64 h_v42 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s36, hinv36, h_v44⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v37 dropping h_v42 h_v43 hinv35 s35 v42 v43
  store_step with Store.apply_rep s36 v37 v44 _ _ hinv36 h64 h_v37 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s37, hinv37, h_v45⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 dropping h_v37 h_v44 hinv36 s36 v37 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_and.construct s37 e_v46 (by rw [he_v46]; exact empty_args) hinv37 h64 as ⟨v46, s38, hinv38, h_v46⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 dropping he_v46 hinv37 e_v46 s37
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__3d.construct s38 e_v47 (by rw [he_v47]; exact empty_args) hinv38 h64 as ⟨v47, s39, hinv39, h_v47⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 dropping he_v47 hinv38 e_v47 s38
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo__40purify.construct s39 e_v48 (by rw [he_v48]; exact empty_args) hinv39 h64 as ⟨v48, s40, hinv40, h_v48⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v47 dropping he_v48 hinv39 e_v48 s39
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre_5fall.construct s40 e_v49 (by rw [he_v49]; exact empty_args) hinv40 h64 as ⟨v49, s41, hinv41, h_v49⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v47 h_v48 dropping he_v49 hinv40 e_v49 s40
  store_step with Store.apply_rep s41 v49 v8 _ _ hinv41 h64 h_v49 h_v8 (by ns_tac) (by ns_tac) as ⟨v50, s42, hinv42, h_v50⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v47 h_v48 dropping h_v49 hinv41 s41 v49
  store_step with Store.apply_rep s42 v50 v5 _ _ hinv42 h64 h_v50 h_v5 (by ns_tac) (by ns_tac) as ⟨v51, s43, hinv43, h_v51⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v47 h_v48 dropping h_v50 hinv42 s42 v50
  store_step with Store.apply_rep s43 v51 v2 _ _ hinv43 h64 h_v51 h_v2 (by ns_tac) (by ns_tac) as ⟨v52, s44, hinv44, h_v52⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v47 h_v48 dropping h_v51 hinv43 s43 v51
  store_step with Store.apply_rep s44 v48 v52 _ _ hinv44 h64 h_v48 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s45, hinv45, h_v53⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v47 dropping h_v48 h_v52 hinv44 s44 v48 v52
  store_step with Store.apply_rep s45 v47 v53 _ _ hinv45 h64 h_v47 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s46, hinv46, h_v54⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 dropping h_v47 h_v53 hinv45 s45 v47 v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct s46 e_v55 (by rw [he_v55]; exact empty_args) hinv46 h64 as ⟨v55, s47, hinv47, h_v55⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v54 dropping he_v55 hinv46 e_v55 s46
  store_step with Store.apply_rep s47 v55 v8 _ _ hinv47 h64 h_v55 h_v8 (by ns_tac) (by ns_tac) as ⟨v56, s48, hinv48, h_v56⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v54 dropping h_v55 hinv47 s47 v55
  store_step with Store.apply_rep s48 v56 v5 _ _ hinv48 h64 h_v56 h_v5 (by ns_tac) (by ns_tac) as ⟨v57, s49, hinv49, h_v57⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v54 dropping h_v56 hinv48 s48 v56
  store_step with Store.apply_rep s49 v57 v2 _ _ hinv49 h64 h_v57 h_v2 (by ns_tac) (by ns_tac) as ⟨v58, s50, hinv50, h_v58⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v54 dropping h_v57 hinv49 s49 v57
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s50 0#u32 (0) (by scalar_tac) hinv50 h64 as ⟨v59, s51, hinv51, h_v59⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v54 h_v58 dropping hinv50 s50
  store_step with Store.apply_rep s51 v58 v59 _ _ hinv51 h64 h_v58 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s52, hinv52, h_v60⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 h_v54 dropping h_v58 h_v59 hinv51 s51 v58 v59
  store_step with Store.apply_rep s52 v54 v60 _ _ hinv52 h64 h_v54 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s53, hinv53, h_v61⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v46 dropping h_v54 h_v60 hinv52 s52 v54 v60
  store_step with Store.apply_rep s53 v46 v61 _ _ hinv53 h64 h_v46 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s54, hinv54, h_v62⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 dropping h_v46 h_v61 hinv53 s53 v46 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_and.construct s54 e_v63 (by rw [he_v63]; exact empty_args) hinv54 h64 as ⟨v63, s55, hinv55, h_v63⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 dropping he_v63 hinv54 e_v63 s54
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo__3d.construct s55 e_v64 (by rw [he_v64]; exact empty_args) hinv55 h64 as ⟨v64, s56, hinv56, h_v64⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 dropping he_v64 hinv55 e_v64 s55
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct s56 e_v65 (by rw [he_v65]; exact empty_args) hinv56 h64 as ⟨v65, s57, hinv57, h_v65⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 dropping he_v65 hinv56 e_v65 s56
  store_step with Store.apply_rep s57 v65 v8 _ _ hinv57 h64 h_v65 h_v8 (by ns_tac) (by ns_tac) as ⟨v66, s58, hinv58, h_v66⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 dropping h_v65 hinv57 s57 v65
  store_step with Store.apply_rep s58 v66 v5 _ _ hinv58 h64 h_v66 h_v5 (by ns_tac) (by ns_tac) as ⟨v67, s59, hinv59, h_v67⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 dropping h_v66 hinv58 s58 v66
  store_step with Store.apply_rep s59 v67 v2 _ _ hinv59 h64 h_v67 h_v2 (by ns_tac) (by ns_tac) as ⟨v68, s60, hinv60, h_v68⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 dropping h_v67 hinv59 s59 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s60 e_v69 (by rw [he_v69]; exact empty_args) hinv60 h64 as ⟨v69, s61, hinv61, h_v69⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 h_v68 dropping he_v69 hinv60 e_v69 s60
  store_step with Store.apply_rep s61 v69 v8 _ _ hinv61 h64 h_v69 h_v8 (by ns_tac) (by ns_tac) as ⟨v70, s62, hinv62, h_v70⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 h_v68 dropping h_v69 hinv61 s61 v69
  store_step with Store.apply_rep s62 v70 v5 _ _ hinv62 h64 h_v70 h_v5 (by ns_tac) (by ns_tac) as ⟨v71, s63, hinv63, h_v71⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 h_v68 dropping h_v70 hinv62 s62 v70
  store_step with Store.apply_rep s63 v68 v71 _ _ hinv63 h64 h_v68 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s64, hinv64, h_v72⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v64 dropping h_v68 h_v71 hinv63 s63 v68 v71
  store_step with Store.apply_rep s64 v64 v72 _ _ hinv64 h64 h_v64 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s65, hinv65, h_v73⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 dropping h_v64 h_v72 hinv64 s64 v64 v72
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s65 e_v74 (by rw [he_v74]; exact empty_args) hinv65 h64 as ⟨v74, s66, hinv66, h_v74⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 dropping he_v74 hinv65 e_v74 s65
  store_step with Store.apply_rep s66 v74 v8 _ _ hinv66 h64 h_v74 h_v8 (by ns_tac) (by ns_tac) as ⟨v75, s67, hinv67, h_v75⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 dropping h_v74 hinv66 s66 v74
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s67 e_v76 (by rw [he_v76]; exact empty_args) hinv67 h64 as ⟨v76, s68, hinv68, h_v76⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 dropping he_v76 hinv67 e_v76 s67
  store_step with Store.apply_rep s68 v76 v8 _ _ hinv68 h64 h_v76 h_v8 (by ns_tac) (by ns_tac) as ⟨v77, s69, hinv69, h_v77⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 dropping h_v76 hinv68 s68 v76
  store_step with Store.apply_rep s69 v77 v5 _ _ hinv69 h64 h_v77 h_v5 (by ns_tac) (by ns_tac) as ⟨v78, s70, hinv70, h_v78⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 dropping h_v77 hinv69 s69 v77
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s70 e_v79 (by rw [he_v79]; exact empty_args) hinv70 h64 as ⟨v79, s71, hinv71, h_v79⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 h_v78 dropping he_v79 hinv70 e_v79 s70
  store_step with Store.apply_rep s71 v79 v8 _ _ hinv71 h64 h_v79 h_v8 (by ns_tac) (by ns_tac) as ⟨v80, s72, hinv72, h_v80⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 h_v78 dropping h_v79 hinv71 s71 v79
  store_step with Store.apply_rep s72 v80 v5 _ _ hinv72 h64 h_v80 h_v5 (by ns_tac) (by ns_tac) as ⟨v81, s73, hinv73, h_v81⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 h_v78 dropping h_v80 hinv72 s72 v80
  store_step with Store.apply_rep s73 v78 v81 _ _ hinv73 h64 h_v78 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s74, hinv74, h_v82⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v75 dropping h_v78 h_v81 hinv73 s73 v78 v81
  store_step with Store.apply_rep s74 v75 v82 _ _ hinv74 h64 h_v75 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s75, hinv75, h_v83⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 dropping h_v75 h_v82 hinv74 s74 v75 v82
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_str_2elen.construct s75 e_v84 (by rw [he_v84]; exact empty_args) hinv75 h64 as ⟨v84, s76, hinv76, h_v84⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v83 dropping he_v84 hinv75 e_v84 s75
  store_step with Store.apply_rep s76 v84 v8 _ _ hinv76 h64 h_v84 h_v8 (by ns_tac) (by ns_tac) as ⟨v85, s77, hinv77, h_v85⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 h_v83 dropping h_v84 hinv76 s76 v84
  store_step with Store.apply_rep s77 v83 v85 _ _ hinv77 h64 h_v83 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s78, hinv78, h_v86⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 h_v73 dropping h_v83 h_v85 hinv77 s77 v83 v85
  store_step with Store.apply_rep s78 v73 v86 _ _ hinv78 h64 h_v73 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s79, hinv79, h_v87⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v63 dropping h_v73 h_v86 hinv78 s78 v73 v86
  store_step with Store.apply_rep s79 v63 v87 _ _ hinv79 h64 h_v63 h_v87 (by ns_tac) (by ns_tac) as ⟨v88, s80, hinv80, h_v88⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 dropping h_v63 h_v87 hinv79 s79 v63 v87
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo_and.construct s80 e_v89 (by rw [he_v89]; exact empty_args) hinv80 h64 as ⟨v89, s81, hinv81, h_v89⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 dropping he_v89 hinv80 e_v89 s80
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo__3d.construct s81 e_v90 (by rw [he_v90]; exact empty_args) hinv81 h64 as ⟨v90, s82, hinv82, h_v90⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 dropping he_v90 hinv81 e_v90 s81
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s82 e_v91 (by rw [he_v91]; exact empty_args) hinv82 h64 as ⟨v91, s83, hinv83, h_v91⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 h_v90 dropping he_v91 hinv82 e_v91 s82
  store_step with Store.apply_rep s83 v91 v8 _ _ hinv83 h64 h_v91 h_v8 (by ns_tac) (by ns_tac) as ⟨v92, s84, hinv84, h_v92⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 h_v90 dropping h_v91 hinv83 s83 v91
  store_step with Store.apply_rep s84 v92 v5 _ _ hinv84 h64 h_v92 h_v5 (by ns_tac) (by ns_tac) as ⟨v93, s85, hinv85, h_v93⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 h_v90 dropping h_v92 hinv84 s84 v92
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s85 0#u32 (0) (by scalar_tac) hinv85 h64 as ⟨v94, s86, hinv86, h_v94⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 h_v90 h_v93 dropping hinv85 s85
  store_step with Store.apply_rep s86 v93 v94 _ _ hinv86 h64 h_v93 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s87, hinv87, h_v95⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 h_v90 dropping h_v93 h_v94 hinv86 s86 v93 v94
  store_step with Store.apply_rep s87 v90 v95 _ _ hinv87 h64 h_v90 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s88, hinv88, h_v96⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 dropping h_v90 h_v95 hinv87 s87 v90 v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s88 0#u32 (0) (by scalar_tac) hinv88 h64 as ⟨v97, s89, hinv89, h_v97⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 h_v96 dropping hinv88 s88
  store_step with Store.apply_rep s89 v96 v97 _ _ hinv89 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s90, hinv90, h_v98⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v89 dropping h_v96 h_v97 hinv89 s89 v96 v97
  store_step with Store.apply_rep s90 v89 v98 _ _ hinv90 h64 h_v89 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s91, hinv91, h_v99⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 dropping h_v89 h_v98 hinv90 s90 v89 v98
  step as ⟨e_v100, he_v100⟩
  store_step with CtorSpec.eo_and.construct s91 e_v100 (by rw [he_v100]; exact empty_args) hinv91 h64 as ⟨v100, s92, hinv92, h_v100⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 dropping he_v100 hinv91 e_v100 s91
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo__3d.construct s92 e_v101 (by rw [he_v101]; exact empty_args) hinv92 h64 as ⟨v101, s93, hinv93, h_v101⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 dropping he_v101 hinv92 e_v101 s92
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s93 e_v102 (by rw [he_v102]; exact empty_args) hinv93 h64 as ⟨v102, s94, hinv94, h_v102⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 dropping he_v102 hinv93 e_v102 s93
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s94 e_v103 (by rw [he_v103]; exact empty_args) hinv94 h64 as ⟨v103, s95, hinv95, h_v103⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 dropping he_v103 hinv94 e_v103 s94
  store_step with Store.apply_rep s95 v103 v8 _ _ hinv95 h64 h_v103 h_v8 (by ns_tac) (by ns_tac) as ⟨v104, s96, hinv96, h_v104⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 dropping h_v103 hinv95 s95 v103
  step as ⟨e_v105, he_v105⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s96 e_v105 (by rw [he_v105]; exact empty_args) hinv96 h64 as ⟨v105, s97, hinv97, h_v105⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 dropping he_v105 hinv96 e_v105 s96
  store_step with Store.apply_rep s97 v105 v8 _ _ hinv97 h64 h_v105 h_v8 (by ns_tac) (by ns_tac) as ⟨v106, s98, hinv98, h_v106⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 dropping h_v105 hinv97 s97 v105
  store_step with Store.apply_rep s98 v106 v5 _ _ hinv98 h64 h_v106 h_v5 (by ns_tac) (by ns_tac) as ⟨v107, s99, hinv99, h_v107⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 dropping h_v106 hinv98 s98 v106
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s99 e_v108 (by rw [he_v108]; exact empty_args) hinv99 h64 as ⟨v108, s100, hinv100, h_v108⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 h_v107 dropping he_v108 hinv99 e_v108 s99
  store_step with Store.apply_rep s100 v108 v8 _ _ hinv100 h64 h_v108 h_v8 (by ns_tac) (by ns_tac) as ⟨v109, s101, hinv101, h_v109⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 h_v107 dropping h_v108 hinv100 s100 v108
  store_step with Store.apply_rep s101 v109 v5 _ _ hinv101 h64 h_v109 h_v5 (by ns_tac) (by ns_tac) as ⟨v110, s102, hinv102, h_v110⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 h_v107 dropping h_v109 hinv101 s101 v109
  store_step with Store.apply_rep s102 v107 v110 _ _ hinv102 h64 h_v107 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s103, hinv103, h_v111⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v104 dropping h_v107 h_v110 hinv102 s102 v107 v110
  store_step with Store.apply_rep s103 v104 v111 _ _ hinv103 h64 h_v104 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s104, hinv104, h_v112⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 dropping h_v104 h_v111 hinv103 s103 v104 v111
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_str_2elen.construct s104 e_v113 (by rw [he_v113]; exact empty_args) hinv104 h64 as ⟨v113, s105, hinv105, h_v113⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v112 dropping he_v113 hinv104 e_v113 s104
  store_step with Store.apply_rep s105 v113 v8 _ _ hinv105 h64 h_v113 h_v8 (by ns_tac) (by ns_tac) as ⟨v114, s106, hinv106, h_v114⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 h_v112 dropping h_v113 hinv105 s105 v113
  store_step with Store.apply_rep s106 v112 v114 _ _ hinv106 h64 h_v112 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s107, hinv107, h_v115⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v102 dropping h_v112 h_v114 hinv106 s106 v112 v114
  store_step with Store.apply_rep s107 v102 v115 _ _ hinv107 h64 h_v102 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s108, hinv108, h_v116⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 dropping h_v102 h_v115 hinv107 s107 v102 v115
  step as ⟨e_v117, he_v117⟩
  store_step with CtorSpec.eo_re_2ediff.construct s108 e_v117 (by rw [he_v117]; exact empty_args) hinv108 h64 as ⟨v117, s109, hinv109, h_v117⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v116 dropping he_v117 hinv108 e_v117 s108
  store_step with Store.apply_rep s109 v117 v5 _ _ hinv109 h64 h_v117 h_v5 (by ns_tac) (by ns_tac) as ⟨v118, s110, hinv110, h_v118⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v116 dropping h_v117 hinv109 s109 v117
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s110 e_v119 (by rw [he_v119]; exact empty_args) hinv110 h64 as ⟨v119, s111, hinv111, h_v119⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v116 h_v118 dropping he_v119 hinv110 e_v119 s110
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s111 _ _ rfl hinv111 h64 as ⟨v120, s112, hinv112, h_v120⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v116 h_v118 h_v119 dropping hinv111 s111
  store_step with Store.apply_rep s112 v119 v120 _ _ hinv112 h64 h_v119 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s113, hinv113, h_v121⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v116 h_v118 dropping h_v119 h_v120 hinv112 s112 v119 v120
  store_step with Store.apply_rep s113 v118 v121 _ _ hinv113 h64 h_v118 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s114, hinv114, h_v122⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v116 dropping h_v118 h_v121 hinv113 s113 v118 v121
  store_step with Store.apply_rep s114 v116 v122 _ _ hinv114 h64 h_v116 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s115, hinv115, h_v123⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 dropping h_v116 h_v122 hinv114 s114 v116 v122
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s115 0#u32 (0) (by scalar_tac) hinv115 h64 as ⟨v124, s116, hinv116, h_v124⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 h_v123 dropping hinv115 s115
  store_step with Store.apply_rep s116 v123 v124 _ _ hinv116 h64 h_v123 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s117, hinv117, h_v125⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v101 dropping h_v123 h_v124 hinv116 s116 v123 v124
  store_step with Store.apply_rep s117 v101 v125 _ _ hinv117 h64 h_v101 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s118, hinv118, h_v126⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 dropping h_v101 h_v125 hinv117 s117 v101 v125
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s118 1#u32 (-1) (by scalar_tac) hinv118 h64 as ⟨v127, s119, hinv119, h_v127⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 h_v126 dropping hinv118 s118
  store_step with Store.apply_rep s119 v126 v127 _ _ hinv119 h64 h_v126 h_v127 (by ns_tac) (by ns_tac) as ⟨v128, s120, hinv120, h_v128⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v100 dropping h_v126 h_v127 hinv119 s119 v126 v127
  store_step with Store.apply_rep s120 v100 v128 _ _ hinv120 h64 h_v100 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s121, hinv121, h_v129⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 dropping h_v100 h_v128 hinv120 s120 v100 v128
  step as ⟨e_v130, he_v130⟩
  store_step with CtorSpec.eo_and.construct s121 e_v130 (by rw [he_v130]; exact empty_args) hinv121 h64 as ⟨v130, s122, hinv122, h_v130⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 dropping he_v130 hinv121 e_v130 s121
  step as ⟨e_v131, he_v131⟩
  store_step with CtorSpec.eo_forall.construct s122 e_v131 (by rw [he_v131]; exact empty_args) hinv122 h64 as ⟨v131, s123, hinv123, h_v131⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 dropping he_v131 hinv122 e_v131 s122
  step as ⟨e_v132, he_v132⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s123 e_v132 (by rw [he_v132]; exact empty_args) hinv123 h64 as ⟨v132, s124, hinv124, h_v132⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 dropping he_v132 hinv123 e_v132 s123
  step as ⟨e_v133, he_v133⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s124 _ _ rfl hinv124 h64 as ⟨v133, s125, hinv125, h_v133⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 h_v132 dropping hinv124 s124
  replace h_v133 := Represents.rep_of_eq h_v133 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v133]; decide)
  step as ⟨e_v134, he_v134⟩
  store_step with CtorSpec.eo_Int.construct s125 e_v134 (by rw [he_v134]; exact empty_args) hinv125 h64 as ⟨v134, s126, hinv126, h_v134⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 h_v132 h_v133 dropping he_v133 he_v134 hinv125 e_v133 e_v134 s125
  step as ⟨e_v135, he_v135⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s126 e_v135 (by rw [he_v135]; rfl) h_v133 h_v134 hinv126 h64 as ⟨v135, s127, hinv127, h_v135⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 h_v132 dropping h_v133 h_v134 he_v135 hinv126 e_v135 s126 v133 v134
  store_step with Store.apply_rep s127 v132 v135 _ _ hinv127 h64 h_v132 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s128, hinv128, h_v136⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 dropping h_v132 h_v135 hinv127 s127 v132 v135
  step as ⟨e_v137, he_v137⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s128 e_v137 (by rw [he_v137]; exact empty_args) hinv128 h64 as ⟨v137, s129, hinv129, h_v137⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 h_v136 dropping he_v137 hinv128 e_v137 s128
  store_step with Store.apply_rep s129 v136 v137 _ _ hinv129 h64 h_v136 h_v137 (by ns_tac) (by ns_tac) as ⟨v138, s130, hinv130, h_v138⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v131 dropping h_v136 h_v137 hinv129 s129 v136 v137
  store_step with Store.apply_rep s130 v131 v138 _ _ hinv130 h64 h_v131 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s131, hinv131, h_v139⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 dropping h_v131 h_v138 hinv130 s130 v131 v138
  step as ⟨e_v140, he_v140⟩
  store_step with CtorSpec.eo_or.construct s131 e_v140 (by rw [he_v140]; exact empty_args) hinv131 h64 as ⟨v140, s132, hinv132, h_v140⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 dropping he_v140 hinv131 e_v140 s131
  step as ⟨e_v141, he_v141⟩
  store_step with CtorSpec.eo_not.construct s132 e_v141 (by rw [he_v141]; exact empty_args) hinv132 h64 as ⟨v141, s133, hinv133, h_v141⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 dropping he_v141 hinv132 e_v141 s132
  step as ⟨e_v142, he_v142⟩
  store_step with CtorSpec.eo__3e_3d.construct s133 e_v142 (by rw [he_v142]; exact empty_args) hinv133 h64 as ⟨v142, s134, hinv134, h_v142⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 dropping he_v142 hinv133 e_v142 s133
  step as ⟨e_v143, he_v143⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s134 _ _ rfl hinv134 h64 as ⟨v143, s135, hinv135, h_v143⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 h_v142 dropping hinv134 s134
  replace h_v143 := Represents.rep_of_eq h_v143 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v143]; decide)
  step as ⟨e_v144, he_v144⟩
  store_step with CtorSpec.eo_Int.construct s135 e_v144 (by rw [he_v144]; exact empty_args) hinv135 h64 as ⟨v144, s136, hinv136, h_v144⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 h_v142 h_v143 dropping he_v143 he_v144 hinv135 e_v143 e_v144 s135
  step as ⟨e_v145, he_v145⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s136 e_v145 (by rw [he_v145]; rfl) h_v143 h_v144 hinv136 h64 as ⟨v145, s137, hinv137, h_v145⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 h_v142 dropping h_v143 h_v144 he_v145 hinv136 e_v145 s136 v143 v144
  store_step with Store.apply_rep s137 v142 v145 _ _ hinv137 h64 h_v142 h_v145 (by ns_tac) (by ns_tac) as ⟨v146, s138, hinv138, h_v146⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 dropping h_v142 h_v145 hinv137 s137 v142 v145
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s138 0#u32 (0) (by scalar_tac) hinv138 h64 as ⟨v147, s139, hinv139, h_v147⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 h_v146 dropping hinv138 s138
  store_step with Store.apply_rep s139 v146 v147 _ _ hinv139 h64 h_v146 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s140, hinv140, h_v148⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 h_v141 dropping h_v146 h_v147 hinv139 s139 v146 v147
  store_step with Store.apply_rep s140 v141 v148 _ _ hinv140 h64 h_v141 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s141, hinv141, h_v149⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v140 dropping h_v141 h_v148 hinv140 s140 v141 v148
  store_step with Store.apply_rep s141 v140 v149 _ _ hinv141 h64 h_v140 h_v149 (by ns_tac) (by ns_tac) as ⟨v150, s142, hinv142, h_v150⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 dropping h_v140 h_v149 hinv141 s141 v140 v149
  step as ⟨e_v151, he_v151⟩
  store_step with CtorSpec.eo_or.construct s142 e_v151 (by rw [he_v151]; exact empty_args) hinv142 h64 as ⟨v151, s143, hinv143, h_v151⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 dropping he_v151 hinv142 e_v151 s142
  step as ⟨e_v152, he_v152⟩
  store_step with CtorSpec.eo_not.construct s143 e_v152 (by rw [he_v152]; exact empty_args) hinv143 h64 as ⟨v152, s144, hinv144, h_v152⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 dropping he_v152 hinv143 e_v152 s143
  step as ⟨e_v153, he_v153⟩
  store_step with CtorSpec.eo__3c.construct s144 e_v153 (by rw [he_v153]; exact empty_args) hinv144 h64 as ⟨v153, s145, hinv145, h_v153⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 dropping he_v153 hinv144 e_v153 s144
  step as ⟨e_v154, he_v154⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s145 _ _ rfl hinv145 h64 as ⟨v154, s146, hinv146, h_v154⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 h_v153 dropping hinv145 s145
  replace h_v154 := Represents.rep_of_eq h_v154 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v154]; decide)
  step as ⟨e_v155, he_v155⟩
  store_step with CtorSpec.eo_Int.construct s146 e_v155 (by rw [he_v155]; exact empty_args) hinv146 h64 as ⟨v155, s147, hinv147, h_v155⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 h_v153 h_v154 dropping he_v154 he_v155 hinv146 e_v154 e_v155 s146
  step as ⟨e_v156, he_v156⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s147 e_v156 (by rw [he_v156]; rfl) h_v154 h_v155 hinv147 h64 as ⟨v156, s148, hinv148, h_v156⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 h_v153 dropping h_v154 h_v155 he_v156 hinv147 e_v156 s147 v154 v155
  store_step with Store.apply_rep s148 v153 v156 _ _ hinv148 h64 h_v153 h_v156 (by ns_tac) (by ns_tac) as ⟨v157, s149, hinv149, h_v157⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 dropping h_v153 h_v156 hinv148 s148 v153 v156
  step as ⟨e_v158, he_v158⟩
  store_step with CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct s149 e_v158 (by rw [he_v158]; exact empty_args) hinv149 h64 as ⟨v158, s150, hinv150, h_v158⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 h_v157 dropping he_v158 hinv149 e_v158 s149
  store_step with Store.apply_rep s150 v158 v8 _ _ hinv150 h64 h_v158 h_v8 (by ns_tac) (by ns_tac) as ⟨v159, s151, hinv151, h_v159⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 h_v157 dropping h_v158 hinv150 s150 v158
  store_step with Store.apply_rep s151 v159 v5 _ _ hinv151 h64 h_v159 h_v5 (by ns_tac) (by ns_tac) as ⟨v160, s152, hinv152, h_v160⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 h_v157 dropping h_v159 hinv151 s151 v159
  store_step with Store.apply_rep s152 v157 v160 _ _ hinv152 h64 h_v157 h_v160 (by ns_tac) (by ns_tac) as ⟨v161, s153, hinv153, h_v161⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 h_v152 dropping h_v157 h_v160 hinv152 s152 v157 v160
  store_step with Store.apply_rep s153 v152 v161 _ _ hinv153 h64 h_v152 h_v161 (by ns_tac) (by ns_tac) as ⟨v162, s154, hinv154, h_v162⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v151 dropping h_v152 h_v161 hinv153 s153 v152 v161
  store_step with Store.apply_rep s154 v151 v162 _ _ hinv154 h64 h_v151 h_v162 (by ns_tac) (by ns_tac) as ⟨v163, s155, hinv155, h_v163⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 dropping h_v151 h_v162 hinv154 s154 v151 v162
  step as ⟨e_v164, he_v164⟩
  store_step with CtorSpec.eo_or.construct s155 e_v164 (by rw [he_v164]; exact empty_args) hinv155 h64 as ⟨v164, s156, hinv156, h_v164⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 dropping he_v164 hinv155 e_v164 s155
  step as ⟨e_v165, he_v165⟩
  store_step with CtorSpec.eo_and.construct s156 e_v165 (by rw [he_v165]; exact empty_args) hinv156 h64 as ⟨v165, s157, hinv157, h_v165⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 dropping he_v165 hinv156 e_v165 s156
  step as ⟨e_v166, he_v166⟩
  store_step with CtorSpec.eo__3e.construct s157 e_v166 (by rw [he_v166]; exact empty_args) hinv157 h64 as ⟨v166, s158, hinv158, h_v166⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 dropping he_v166 hinv157 e_v166 s157
  step as ⟨e_v167, he_v167⟩
  store_step with CtorSpec.eo__2d.construct s158 e_v167 (by rw [he_v167]; exact empty_args) hinv158 h64 as ⟨v167, s159, hinv159, h_v167⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 dropping he_v167 hinv158 e_v167 s158
  step as ⟨e_v168, he_v168⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s159 e_v168 (by rw [he_v168]; exact empty_args) hinv159 h64 as ⟨v168, s160, hinv160, h_v168⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 dropping he_v168 hinv159 e_v168 s159
  store_step with Store.apply_rep s160 v168 v8 _ _ hinv160 h64 h_v168 h_v8 (by ns_tac) (by ns_tac) as ⟨v169, s161, hinv161, h_v169⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 dropping h_v168 hinv160 s160 v168
  store_step with Store.apply_rep s161 v169 v5 _ _ hinv161 h64 h_v169 h_v5 (by ns_tac) (by ns_tac) as ⟨v170, s162, hinv162, h_v170⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 dropping h_v169 hinv161 s161 v169
  step as ⟨e_v171, he_v171⟩
  store_step with CtorSpec.eo__2b.construct s162 e_v171 (by rw [he_v171]; exact empty_args) hinv162 h64 as ⟨v171, s163, hinv163, h_v171⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 dropping he_v171 hinv162 e_v171 s162
  step as ⟨e_v172, he_v172⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s163 _ _ rfl hinv163 h64 as ⟨v172, s164, hinv164, h_v172⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v171 dropping hinv163 s163
  replace h_v172 := Represents.rep_of_eq h_v172 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v172]; decide)
  step as ⟨e_v173, he_v173⟩
  store_step with CtorSpec.eo_Int.construct s164 e_v173 (by rw [he_v173]; exact empty_args) hinv164 h64 as ⟨v173, s165, hinv165, h_v173⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v171 h_v172 dropping he_v172 he_v173 hinv164 e_v172 e_v173 s164
  step as ⟨e_v174, he_v174⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s165 e_v174 (by rw [he_v174]; rfl) h_v172 h_v173 hinv165 h64 as ⟨v174, s166, hinv166, h_v174⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v171 dropping h_v172 h_v173 he_v174 hinv165 e_v174 s165 v172 v173
  store_step with Store.apply_rep s166 v171 v174 _ _ hinv166 h64 h_v171 h_v174 (by ns_tac) (by ns_tac) as ⟨v175, s167, hinv167, h_v175⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 dropping h_v171 h_v174 hinv166 s166 v171 v174
  step as ⟨e_v176, he_v176⟩
  store_step with CtorSpec.eo__2b.construct s167 e_v176 (by rw [he_v176]; exact empty_args) hinv167 h64 as ⟨v176, s168, hinv168, h_v176⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v175 dropping he_v176 hinv167 e_v176 s167
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s168 1#u32 (1) (by scalar_tac) hinv168 h64 as ⟨v177, s169, hinv169, h_v177⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v175 h_v176 dropping hinv168 s168
  store_step with Store.apply_rep s169 v176 v177 _ _ hinv169 h64 h_v176 h_v177 (by ns_tac) (by ns_tac) as ⟨v178, s170, hinv170, h_v178⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v175 dropping h_v176 h_v177 hinv169 s169 v176 v177
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s170 0#u32 (0) (by scalar_tac) hinv170 h64 as ⟨v179, s171, hinv171, h_v179⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v175 h_v178 dropping hinv170 s170
  store_step with Store.apply_rep s171 v178 v179 _ _ hinv171 h64 h_v178 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s172, hinv172, h_v180⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 h_v175 dropping h_v178 h_v179 hinv171 s171 v178 v179
  store_step with Store.apply_rep s172 v175 v180 _ _ hinv172 h64 h_v175 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s173, hinv173, h_v181⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 h_v170 dropping h_v175 h_v180 hinv172 s172 v175 v180
  store_step with Store.apply_rep s173 v170 v181 _ _ hinv173 h64 h_v170 h_v181 (by ns_tac) (by ns_tac) as ⟨v182, s174, hinv174, h_v182⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v167 dropping h_v170 h_v181 hinv173 s173 v170 v181
  store_step with Store.apply_rep s174 v167 v182 _ _ hinv174 h64 h_v167 h_v182 (by ns_tac) (by ns_tac) as ⟨v183, s175, hinv175, h_v183⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 dropping h_v167 h_v182 hinv174 s174 v167 v182
  step as ⟨e_v184, he_v184⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s175 e_v184 (by rw [he_v184]; exact empty_args) hinv175 h64 as ⟨v184, s176, hinv176, h_v184⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 dropping he_v184 hinv175 e_v184 s175
  store_step with Store.apply_rep s176 v184 v8 _ _ hinv176 h64 h_v184 h_v8 (by ns_tac) (by ns_tac) as ⟨v185, s177, hinv177, h_v185⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 dropping h_v184 hinv176 s176 v184
  step as ⟨e_v186, he_v186⟩
  store_step with CtorSpec.eo_re_2ediff.construct s177 e_v186 (by rw [he_v186]; exact empty_args) hinv177 h64 as ⟨v186, s178, hinv178, h_v186⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v185 dropping he_v186 hinv177 e_v186 s177
  store_step with Store.apply_rep s178 v186 v5 _ _ hinv178 h64 h_v186 h_v5 (by ns_tac) (by ns_tac) as ⟨v187, s179, hinv179, h_v187⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v185 dropping h_v186 hinv178 s178 v186
  step as ⟨e_v188, he_v188⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s179 e_v188 (by rw [he_v188]; exact empty_args) hinv179 h64 as ⟨v188, s180, hinv180, h_v188⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v185 h_v187 dropping he_v188 hinv179 e_v188 s179
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s180 _ _ rfl hinv180 h64 as ⟨v189, s181, hinv181, h_v189⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v185 h_v187 h_v188 dropping hinv180 s180
  store_step with Store.apply_rep s181 v188 v189 _ _ hinv181 h64 h_v188 h_v189 (by ns_tac) (by ns_tac) as ⟨v190, s182, hinv182, h_v190⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v185 h_v187 dropping h_v188 h_v189 hinv181 s181 v188 v189
  store_step with Store.apply_rep s182 v187 v190 _ _ hinv182 h64 h_v187 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s183, hinv183, h_v191⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v185 dropping h_v187 h_v190 hinv182 s182 v187 v190
  store_step with Store.apply_rep s183 v185 v191 _ _ hinv183 h64 h_v185 h_v191 (by ns_tac) (by ns_tac) as ⟨v192, s184, hinv184, h_v192⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 dropping h_v185 h_v191 hinv183 s183 v185 v191
  step as ⟨e_v193, he_v193⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s184 e_v193 (by rw [he_v193]; exact empty_args) hinv184 h64 as ⟨v193, s185, hinv185, h_v193⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 dropping he_v193 hinv184 e_v193 s184
  store_step with Store.apply_rep s185 v193 v8 _ _ hinv185 h64 h_v193 h_v8 (by ns_tac) (by ns_tac) as ⟨v194, s186, hinv186, h_v194⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 dropping h_v193 hinv185 s185 v193
  store_step with Store.apply_rep s186 v194 v5 _ _ hinv186 h64 h_v194 h_v5 (by ns_tac) (by ns_tac) as ⟨v195, s187, hinv187, h_v195⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 dropping h_v194 hinv186 s186 v194
  step as ⟨e_v196, he_v196⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s187 _ _ rfl hinv187 h64 as ⟨v196, s188, hinv188, h_v196⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 h_v195 dropping hinv187 s187
  replace h_v196 := Represents.rep_of_eq h_v196 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v196]; decide)
  step as ⟨e_v197, he_v197⟩
  store_step with CtorSpec.eo_Int.construct s188 e_v197 (by rw [he_v197]; exact empty_args) hinv188 h64 as ⟨v197, s189, hinv189, h_v197⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 h_v195 h_v196 dropping he_v196 he_v197 hinv188 e_v196 e_v197 s188
  step as ⟨e_v198, he_v198⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s189 e_v198 (by rw [he_v198]; rfl) h_v196 h_v197 hinv189 h64 as ⟨v198, s190, hinv190, h_v198⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 h_v195 dropping h_v196 h_v197 he_v198 hinv189 e_v198 s189 v196 v197
  store_step with Store.apply_rep s190 v195 v198 _ _ hinv190 h64 h_v195 h_v198 (by ns_tac) (by ns_tac) as ⟨v199, s191, hinv191, h_v199⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 h_v192 dropping h_v195 h_v198 hinv190 s190 v195 v198
  store_step with Store.apply_rep s191 v192 v199 _ _ hinv191 h64 h_v192 h_v199 (by ns_tac) (by ns_tac) as ⟨v200, s192, hinv192, h_v200⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 h_v183 dropping h_v192 h_v199 hinv191 s191 v192 v199
  store_step with Store.apply_rep s192 v183 v200 _ _ hinv192 h64 h_v183 h_v200 (by ns_tac) (by ns_tac) as ⟨v201, s193, hinv193, h_v201⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v166 dropping h_v183 h_v200 hinv192 s192 v183 v200
  store_step with Store.apply_rep s193 v166 v201 _ _ hinv193 h64 h_v166 h_v201 (by ns_tac) (by ns_tac) as ⟨v202, s194, hinv194, h_v202⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 dropping h_v166 h_v201 hinv193 s193 v166 v201
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s194 0#u32 (0) (by scalar_tac) hinv194 h64 as ⟨v203, s195, hinv195, h_v203⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 h_v202 dropping hinv194 s194
  store_step with Store.apply_rep s195 v202 v203 _ _ hinv195 h64 h_v202 h_v203 (by ns_tac) (by ns_tac) as ⟨v204, s196, hinv196, h_v204⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v165 dropping h_v202 h_v203 hinv195 s195 v202 v203
  store_step with Store.apply_rep s196 v165 v204 _ _ hinv196 h64 h_v165 h_v204 (by ns_tac) (by ns_tac) as ⟨v205, s197, hinv197, h_v205⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 dropping h_v165 h_v204 hinv196 s196 v165 v204
  step as ⟨e_v206, he_v206⟩
  store_step with CtorSpec.eo_and.construct s197 e_v206 (by rw [he_v206]; exact empty_args) hinv197 h64 as ⟨v206, s198, hinv198, h_v206⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 dropping he_v206 hinv197 e_v206 s197
  step as ⟨e_v207, he_v207⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s198 e_v207 (by rw [he_v207]; exact empty_args) hinv198 h64 as ⟨v207, s199, hinv199, h_v207⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 dropping he_v207 hinv198 e_v207 s198
  step as ⟨e_v208, he_v208⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s199 e_v208 (by rw [he_v208]; exact empty_args) hinv199 h64 as ⟨v208, s200, hinv200, h_v208⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 dropping he_v208 hinv199 e_v208 s199
  store_step with Store.apply_rep s200 v208 v8 _ _ hinv200 h64 h_v208 h_v8 (by ns_tac) (by ns_tac) as ⟨v209, s201, hinv201, h_v209⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 dropping h_v208 hinv200 s200 v208
  step as ⟨e_v210, he_v210⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s201 e_v210 (by rw [he_v210]; exact empty_args) hinv201 h64 as ⟨v210, s202, hinv202, h_v210⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 dropping he_v210 hinv201 e_v210 s201
  store_step with Store.apply_rep s202 v210 v8 _ _ hinv202 h64 h_v210 h_v8 (by ns_tac) (by ns_tac) as ⟨v211, s203, hinv203, h_v211⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 dropping h_v210 hinv202 s202 v210
  step as ⟨e_v212, he_v212⟩
  store_step with CtorSpec.eo_re_2ediff.construct s203 e_v212 (by rw [he_v212]; exact empty_args) hinv203 h64 as ⟨v212, s204, hinv204, h_v212⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v211 dropping he_v212 hinv203 e_v212 s203
  store_step with Store.apply_rep s204 v212 v5 _ _ hinv204 h64 h_v212 h_v5 (by ns_tac) (by ns_tac) as ⟨v213, s205, hinv205, h_v213⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v211 dropping h_v212 hinv204 s204 v212
  step as ⟨e_v214, he_v214⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s205 e_v214 (by rw [he_v214]; exact empty_args) hinv205 h64 as ⟨v214, s206, hinv206, h_v214⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v211 h_v213 dropping he_v214 hinv205 e_v214 s205
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s206 _ _ rfl hinv206 h64 as ⟨v215, s207, hinv207, h_v215⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v211 h_v213 h_v214 dropping hinv206 s206
  store_step with Store.apply_rep s207 v214 v215 _ _ hinv207 h64 h_v214 h_v215 (by ns_tac) (by ns_tac) as ⟨v216, s208, hinv208, h_v216⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v211 h_v213 dropping h_v214 h_v215 hinv207 s207 v214 v215
  store_step with Store.apply_rep s208 v213 v216 _ _ hinv208 h64 h_v213 h_v216 (by ns_tac) (by ns_tac) as ⟨v217, s209, hinv209, h_v217⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v211 dropping h_v213 h_v216 hinv208 s208 v213 v216
  store_step with Store.apply_rep s209 v211 v217 _ _ hinv209 h64 h_v211 h_v217 (by ns_tac) (by ns_tac) as ⟨v218, s210, hinv210, h_v218⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 dropping h_v211 h_v217 hinv209 s209 v211 v217
  step as ⟨e_v219, he_v219⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s210 e_v219 (by rw [he_v219]; exact empty_args) hinv210 h64 as ⟨v219, s211, hinv211, h_v219⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 dropping he_v219 hinv210 e_v219 s210
  store_step with Store.apply_rep s211 v219 v8 _ _ hinv211 h64 h_v219 h_v8 (by ns_tac) (by ns_tac) as ⟨v220, s212, hinv212, h_v220⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 dropping h_v219 hinv211 s211 v219
  store_step with Store.apply_rep s212 v220 v5 _ _ hinv212 h64 h_v220 h_v5 (by ns_tac) (by ns_tac) as ⟨v221, s213, hinv213, h_v221⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 dropping h_v220 hinv212 s212 v220
  step as ⟨e_v222, he_v222⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s213 _ _ rfl hinv213 h64 as ⟨v222, s214, hinv214, h_v222⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 h_v221 dropping hinv213 s213
  replace h_v222 := Represents.rep_of_eq h_v222 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v222]; decide)
  step as ⟨e_v223, he_v223⟩
  store_step with CtorSpec.eo_Int.construct s214 e_v223 (by rw [he_v223]; exact empty_args) hinv214 h64 as ⟨v223, s215, hinv215, h_v223⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 h_v221 h_v222 dropping he_v222 he_v223 hinv214 e_v222 e_v223 s214
  step as ⟨e_v224, he_v224⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s215 e_v224 (by rw [he_v224]; rfl) h_v222 h_v223 hinv215 h64 as ⟨v224, s216, hinv216, h_v224⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 h_v221 dropping h_v222 h_v223 he_v224 hinv215 e_v224 s215 v222 v223
  store_step with Store.apply_rep s216 v221 v224 _ _ hinv216 h64 h_v221 h_v224 (by ns_tac) (by ns_tac) as ⟨v225, s217, hinv217, h_v225⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 h_v218 dropping h_v221 h_v224 hinv216 s216 v221 v224
  store_step with Store.apply_rep s217 v218 v225 _ _ hinv217 h64 h_v218 h_v225 (by ns_tac) (by ns_tac) as ⟨v226, s218, hinv218, h_v226⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v209 dropping h_v218 h_v225 hinv217 s217 v218 v225
  store_step with Store.apply_rep s218 v209 v226 _ _ hinv218 h64 h_v209 h_v226 (by ns_tac) (by ns_tac) as ⟨v227, s219, hinv219, h_v227⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 dropping h_v209 h_v226 hinv218 s218 v209 v226
  step as ⟨e_v228, he_v228⟩
  store_step with CtorSpec.eo__2d.construct s219 e_v228 (by rw [he_v228]; exact empty_args) hinv219 h64 as ⟨v228, s220, hinv220, h_v228⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 dropping he_v228 hinv219 e_v228 s219
  step as ⟨e_v229, he_v229⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s220 e_v229 (by rw [he_v229]; exact empty_args) hinv220 h64 as ⟨v229, s221, hinv221, h_v229⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 dropping he_v229 hinv220 e_v229 s220
  store_step with Store.apply_rep s221 v229 v8 _ _ hinv221 h64 h_v229 h_v8 (by ns_tac) (by ns_tac) as ⟨v230, s222, hinv222, h_v230⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 dropping h_v229 hinv221 s221 v229
  store_step with Store.apply_rep s222 v230 v5 _ _ hinv222 h64 h_v230 h_v5 (by ns_tac) (by ns_tac) as ⟨v231, s223, hinv223, h_v231⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 dropping h_v230 hinv222 s222 v230
  step as ⟨e_v232, he_v232⟩
  store_step with CtorSpec.eo__2b.construct s223 e_v232 (by rw [he_v232]; exact empty_args) hinv223 h64 as ⟨v232, s224, hinv224, h_v232⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 dropping he_v232 hinv223 e_v232 s223
  step as ⟨e_v233, he_v233⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s224 _ _ rfl hinv224 h64 as ⟨v233, s225, hinv225, h_v233⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v232 dropping hinv224 s224
  replace h_v233 := Represents.rep_of_eq h_v233 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v233]; decide)
  step as ⟨e_v234, he_v234⟩
  store_step with CtorSpec.eo_Int.construct s225 e_v234 (by rw [he_v234]; exact empty_args) hinv225 h64 as ⟨v234, s226, hinv226, h_v234⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v232 h_v233 dropping he_v233 he_v234 hinv225 e_v233 e_v234 s225
  step as ⟨e_v235, he_v235⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s226 e_v235 (by rw [he_v235]; rfl) h_v233 h_v234 hinv226 h64 as ⟨v235, s227, hinv227, h_v235⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v232 dropping h_v233 h_v234 he_v235 hinv226 e_v235 s226 v233 v234
  store_step with Store.apply_rep s227 v232 v235 _ _ hinv227 h64 h_v232 h_v235 (by ns_tac) (by ns_tac) as ⟨v236, s228, hinv228, h_v236⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 dropping h_v232 h_v235 hinv227 s227 v232 v235
  step as ⟨e_v237, he_v237⟩
  store_step with CtorSpec.eo__2b.construct s228 e_v237 (by rw [he_v237]; exact empty_args) hinv228 h64 as ⟨v237, s229, hinv229, h_v237⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v236 dropping he_v237 hinv228 e_v237 s228
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s229 1#u32 (1) (by scalar_tac) hinv229 h64 as ⟨v238, s230, hinv230, h_v238⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v236 h_v237 dropping hinv229 s229
  store_step with Store.apply_rep s230 v237 v238 _ _ hinv230 h64 h_v237 h_v238 (by ns_tac) (by ns_tac) as ⟨v239, s231, hinv231, h_v239⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v236 dropping h_v237 h_v238 hinv230 s230 v237 v238
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s231 0#u32 (0) (by scalar_tac) hinv231 h64 as ⟨v240, s232, hinv232, h_v240⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v236 h_v239 dropping hinv231 s231
  store_step with Store.apply_rep s232 v239 v240 _ _ hinv232 h64 h_v239 h_v240 (by ns_tac) (by ns_tac) as ⟨v241, s233, hinv233, h_v241⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 h_v236 dropping h_v239 h_v240 hinv232 s232 v239 v240
  store_step with Store.apply_rep s233 v236 v241 _ _ hinv233 h64 h_v236 h_v241 (by ns_tac) (by ns_tac) as ⟨v242, s234, hinv234, h_v242⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 h_v231 dropping h_v236 h_v241 hinv233 s233 v236 v241
  store_step with Store.apply_rep s234 v231 v242 _ _ hinv234 h64 h_v231 h_v242 (by ns_tac) (by ns_tac) as ⟨v243, s235, hinv235, h_v243⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v228 dropping h_v231 h_v242 hinv234 s234 v231 v242
  store_step with Store.apply_rep s235 v228 v243 _ _ hinv235 h64 h_v228 h_v243 (by ns_tac) (by ns_tac) as ⟨v244, s236, hinv236, h_v244⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 dropping h_v228 h_v243 hinv235 s235 v228 v243
  step as ⟨e_v245, he_v245⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s236 e_v245 (by rw [he_v245]; exact empty_args) hinv236 h64 as ⟨v245, s237, hinv237, h_v245⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 dropping he_v245 hinv236 e_v245 s236
  store_step with Store.apply_rep s237 v245 v8 _ _ hinv237 h64 h_v245 h_v8 (by ns_tac) (by ns_tac) as ⟨v246, s238, hinv238, h_v246⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 dropping h_v245 hinv237 s237 v245
  step as ⟨e_v247, he_v247⟩
  store_step with CtorSpec.eo_re_2ediff.construct s238 e_v247 (by rw [he_v247]; exact empty_args) hinv238 h64 as ⟨v247, s239, hinv239, h_v247⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v246 dropping he_v247 hinv238 e_v247 s238
  store_step with Store.apply_rep s239 v247 v5 _ _ hinv239 h64 h_v247 h_v5 (by ns_tac) (by ns_tac) as ⟨v248, s240, hinv240, h_v248⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v246 dropping h_v247 hinv239 s239 v247
  step as ⟨e_v249, he_v249⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s240 e_v249 (by rw [he_v249]; exact empty_args) hinv240 h64 as ⟨v249, s241, hinv241, h_v249⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v246 h_v248 dropping he_v249 hinv240 e_v249 s240
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s241 _ _ rfl hinv241 h64 as ⟨v250, s242, hinv242, h_v250⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v246 h_v248 h_v249 dropping hinv241 s241
  store_step with Store.apply_rep s242 v249 v250 _ _ hinv242 h64 h_v249 h_v250 (by ns_tac) (by ns_tac) as ⟨v251, s243, hinv243, h_v251⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v246 h_v248 dropping h_v249 h_v250 hinv242 s242 v249 v250
  store_step with Store.apply_rep s243 v248 v251 _ _ hinv243 h64 h_v248 h_v251 (by ns_tac) (by ns_tac) as ⟨v252, s244, hinv244, h_v252⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v246 dropping h_v248 h_v251 hinv243 s243 v248 v251
  store_step with Store.apply_rep s244 v246 v252 _ _ hinv244 h64 h_v246 h_v252 (by ns_tac) (by ns_tac) as ⟨v253, s245, hinv245, h_v253⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 dropping h_v246 h_v252 hinv244 s244 v246 v252
  step as ⟨e_v254, he_v254⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s245 e_v254 (by rw [he_v254]; exact empty_args) hinv245 h64 as ⟨v254, s246, hinv246, h_v254⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 dropping he_v254 hinv245 e_v254 s245
  store_step with Store.apply_rep s246 v254 v8 _ _ hinv246 h64 h_v254 h_v8 (by ns_tac) (by ns_tac) as ⟨v255, s247, hinv247, h_v255⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 dropping h_v254 hinv246 s246 v254
  store_step with Store.apply_rep s247 v255 v5 _ _ hinv247 h64 h_v255 h_v5 (by ns_tac) (by ns_tac) as ⟨v256, s248, hinv248, h_v256⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 dropping h_v255 hinv247 s247 v255
  step as ⟨e_v257, he_v257⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s248 _ _ rfl hinv248 h64 as ⟨v257, s249, hinv249, h_v257⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 h_v256 dropping hinv248 s248
  replace h_v257 := Represents.rep_of_eq h_v257 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v257]; decide)
  step as ⟨e_v258, he_v258⟩
  store_step with CtorSpec.eo_Int.construct s249 e_v258 (by rw [he_v258]; exact empty_args) hinv249 h64 as ⟨v258, s250, hinv250, h_v258⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 h_v256 h_v257 dropping he_v257 he_v258 hinv249 e_v257 e_v258 s249
  step as ⟨e_v259, he_v259⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s250 e_v259 (by rw [he_v259]; rfl) h_v257 h_v258 hinv250 h64 as ⟨v259, s251, hinv251, h_v259⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 h_v256 dropping h_v257 h_v258 he_v259 hinv250 e_v259 s250 v257 v258
  store_step with Store.apply_rep s251 v256 v259 _ _ hinv251 h64 h_v256 h_v259 (by ns_tac) (by ns_tac) as ⟨v260, s252, hinv252, h_v260⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 h_v253 dropping h_v256 h_v259 hinv251 s251 v256 v259
  store_step with Store.apply_rep s252 v253 v260 _ _ hinv252 h64 h_v253 h_v260 (by ns_tac) (by ns_tac) as ⟨v261, s253, hinv253, h_v261⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 h_v244 dropping h_v253 h_v260 hinv252 s252 v253 v260
  store_step with Store.apply_rep s253 v244 v261 _ _ hinv253 h64 h_v244 h_v261 (by ns_tac) (by ns_tac) as ⟨v262, s254, hinv254, h_v262⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 h_v227 dropping h_v244 h_v261 hinv253 s253 v244 v261
  store_step with Store.apply_rep s254 v227 v262 _ _ hinv254 h64 h_v227 h_v262 (by ns_tac) (by ns_tac) as ⟨v263, s255, hinv255, h_v263⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v207 dropping h_v227 h_v262 hinv254 s254 v227 v262
  store_step with Store.apply_rep s255 v207 v263 _ _ hinv255 h64 h_v207 h_v263 (by ns_tac) (by ns_tac) as ⟨v264, s256, hinv256, h_v264⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 dropping h_v207 h_v263 hinv255 s255 v207 v263
  step as ⟨e_v265, he_v265⟩
  store_step with CtorSpec.eo_re_2ediff.construct s256 e_v265 (by rw [he_v265]; exact empty_args) hinv256 h64 as ⟨v265, s257, hinv257, h_v265⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v264 dropping he_v265 hinv256 e_v265 s256
  store_step with Store.apply_rep s257 v265 v5 _ _ hinv257 h64 h_v265 h_v5 (by ns_tac) (by ns_tac) as ⟨v266, s258, hinv258, h_v266⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v264 dropping h_v265 hinv257 s257 v265
  step as ⟨e_v267, he_v267⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s258 e_v267 (by rw [he_v267]; exact empty_args) hinv258 h64 as ⟨v267, s259, hinv259, h_v267⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v264 h_v266 dropping he_v267 hinv258 e_v267 s258
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s259 _ _ rfl hinv259 h64 as ⟨v268, s260, hinv260, h_v268⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v264 h_v266 h_v267 dropping hinv259 s259
  store_step with Store.apply_rep s260 v267 v268 _ _ hinv260 h64 h_v267 h_v268 (by ns_tac) (by ns_tac) as ⟨v269, s261, hinv261, h_v269⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v264 h_v266 dropping h_v267 h_v268 hinv260 s260 v267 v268
  store_step with Store.apply_rep s261 v266 v269 _ _ hinv261 h64 h_v266 h_v269 (by ns_tac) (by ns_tac) as ⟨v270, s262, hinv262, h_v270⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 h_v264 dropping h_v266 h_v269 hinv261 s261 v266 v269
  store_step with Store.apply_rep s262 v264 v270 _ _ hinv262 h64 h_v264 h_v270 (by ns_tac) (by ns_tac) as ⟨v271, s263, hinv263, h_v271⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v206 dropping h_v264 h_v270 hinv262 s262 v264 v270
  store_step with Store.apply_rep s263 v206 v271 _ _ hinv263 h64 h_v206 h_v271 (by ns_tac) (by ns_tac) as ⟨v272, s264, hinv264, h_v272⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 dropping h_v206 h_v271 hinv263 s263 v206 v271
  step as ⟨e_v273, he_v273⟩
  store_step with CtorSpec.eo_and.construct s264 e_v273 (by rw [he_v273]; exact empty_args) hinv264 h64 as ⟨v273, s265, hinv265, h_v273⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 dropping he_v273 hinv264 e_v273 s264
  step as ⟨e_v274, he_v274⟩
  store_step with CtorSpec.eo_forall.construct s265 e_v274 (by rw [he_v274]; exact empty_args) hinv265 h64 as ⟨v274, s266, hinv266, h_v274⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 dropping he_v274 hinv265 e_v274 s265
  step as ⟨e_v275, he_v275⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s266 e_v275 (by rw [he_v275]; exact empty_args) hinv266 h64 as ⟨v275, s267, hinv267, h_v275⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 dropping he_v275 hinv266 e_v275 s266
  step as ⟨e_v276, he_v276⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s267 _ _ rfl hinv267 h64 as ⟨v276, s268, hinv268, h_v276⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 h_v275 dropping hinv267 s267
  replace h_v276 := Represents.rep_of_eq h_v276 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v276]; decide)
  step as ⟨e_v277, he_v277⟩
  store_step with CtorSpec.eo_Int.construct s268 e_v277 (by rw [he_v277]; exact empty_args) hinv268 h64 as ⟨v277, s269, hinv269, h_v277⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 h_v275 h_v276 dropping he_v276 he_v277 hinv268 e_v276 e_v277 s268
  step as ⟨e_v278, he_v278⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s269 e_v278 (by rw [he_v278]; rfl) h_v276 h_v277 hinv269 h64 as ⟨v278, s270, hinv270, h_v278⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 h_v275 dropping h_v276 h_v277 he_v278 hinv269 e_v278 s269 v276 v277
  store_step with Store.apply_rep s270 v275 v278 _ _ hinv270 h64 h_v275 h_v278 (by ns_tac) (by ns_tac) as ⟨v279, s271, hinv271, h_v279⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 dropping h_v275 h_v278 hinv270 s270 v275 v278
  step as ⟨e_v280, he_v280⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s271 e_v280 (by rw [he_v280]; exact empty_args) hinv271 h64 as ⟨v280, s272, hinv272, h_v280⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 h_v279 dropping he_v280 hinv271 e_v280 s271
  store_step with Store.apply_rep s272 v279 v280 _ _ hinv272 h64 h_v279 h_v280 (by ns_tac) (by ns_tac) as ⟨v281, s273, hinv273, h_v281⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v274 dropping h_v279 h_v280 hinv272 s272 v279 v280
  store_step with Store.apply_rep s273 v274 v281 _ _ hinv273 h64 h_v274 h_v281 (by ns_tac) (by ns_tac) as ⟨v282, s274, hinv274, h_v282⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 dropping h_v274 h_v281 hinv273 s273 v274 v281
  step as ⟨e_v283, he_v283⟩
  store_step with CtorSpec.eo_or.construct s274 e_v283 (by rw [he_v283]; exact empty_args) hinv274 h64 as ⟨v283, s275, hinv275, h_v283⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 dropping he_v283 hinv274 e_v283 s274
  step as ⟨e_v284, he_v284⟩
  store_step with CtorSpec.eo_not.construct s275 e_v284 (by rw [he_v284]; exact empty_args) hinv275 h64 as ⟨v284, s276, hinv276, h_v284⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 dropping he_v284 hinv275 e_v284 s275
  step as ⟨e_v285, he_v285⟩
  store_step with CtorSpec.eo__3e.construct s276 e_v285 (by rw [he_v285]; exact empty_args) hinv276 h64 as ⟨v285, s277, hinv277, h_v285⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 dropping he_v285 hinv276 e_v285 s276
  step as ⟨e_v286, he_v286⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s277 _ _ rfl hinv277 h64 as ⟨v286, s278, hinv278, h_v286⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 h_v285 dropping hinv277 s277
  replace h_v286 := Represents.rep_of_eq h_v286 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v286]; decide)
  step as ⟨e_v287, he_v287⟩
  store_step with CtorSpec.eo_Int.construct s278 e_v287 (by rw [he_v287]; exact empty_args) hinv278 h64 as ⟨v287, s279, hinv279, h_v287⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 h_v285 h_v286 dropping he_v286 he_v287 hinv278 e_v286 e_v287 s278
  step as ⟨e_v288, he_v288⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s279 e_v288 (by rw [he_v288]; rfl) h_v286 h_v287 hinv279 h64 as ⟨v288, s280, hinv280, h_v288⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 h_v285 dropping h_v286 h_v287 he_v288 hinv279 e_v288 s279 v286 v287
  store_step with Store.apply_rep s280 v285 v288 _ _ hinv280 h64 h_v285 h_v288 (by ns_tac) (by ns_tac) as ⟨v289, s281, hinv281, h_v289⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 dropping h_v285 h_v288 hinv280 s280 v285 v288
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s281 0#u32 (0) (by scalar_tac) hinv281 h64 as ⟨v290, s282, hinv282, h_v290⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 h_v289 dropping hinv281 s281
  store_step with Store.apply_rep s282 v289 v290 _ _ hinv282 h64 h_v289 h_v290 (by ns_tac) (by ns_tac) as ⟨v291, s283, hinv283, h_v291⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 h_v284 dropping h_v289 h_v290 hinv282 s282 v289 v290
  store_step with Store.apply_rep s283 v284 v291 _ _ hinv283 h64 h_v284 h_v291 (by ns_tac) (by ns_tac) as ⟨v292, s284, hinv284, h_v292⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v283 dropping h_v284 h_v291 hinv283 s283 v284 v291
  store_step with Store.apply_rep s284 v283 v292 _ _ hinv284 h64 h_v283 h_v292 (by ns_tac) (by ns_tac) as ⟨v293, s285, hinv285, h_v293⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 dropping h_v283 h_v292 hinv284 s284 v283 v292
  step as ⟨e_v294, he_v294⟩
  store_step with CtorSpec.eo_or.construct s285 e_v294 (by rw [he_v294]; exact empty_args) hinv285 h64 as ⟨v294, s286, hinv286, h_v294⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 dropping he_v294 hinv285 e_v294 s285
  step as ⟨e_v295, he_v295⟩
  store_step with CtorSpec.eo_not.construct s286 e_v295 (by rw [he_v295]; exact empty_args) hinv286 h64 as ⟨v295, s287, hinv287, h_v295⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 dropping he_v295 hinv286 e_v295 s286
  step as ⟨e_v296, he_v296⟩
  store_step with CtorSpec.eo__3c.construct s287 e_v296 (by rw [he_v296]; exact empty_args) hinv287 h64 as ⟨v296, s288, hinv288, h_v296⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 dropping he_v296 hinv287 e_v296 s287
  step as ⟨e_v297, he_v297⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s288 _ _ rfl hinv288 h64 as ⟨v297, s289, hinv289, h_v297⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v296 dropping hinv288 s288
  replace h_v297 := Represents.rep_of_eq h_v297 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v297]; decide)
  step as ⟨e_v298, he_v298⟩
  store_step with CtorSpec.eo_Int.construct s289 e_v298 (by rw [he_v298]; exact empty_args) hinv289 h64 as ⟨v298, s290, hinv290, h_v298⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v296 h_v297 dropping he_v297 he_v298 hinv289 e_v297 e_v298 s289
  step as ⟨e_v299, he_v299⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s290 e_v299 (by rw [he_v299]; rfl) h_v297 h_v298 hinv290 h64 as ⟨v299, s291, hinv291, h_v299⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v296 dropping h_v297 h_v298 he_v299 hinv290 e_v299 s290 v297 v298
  store_step with Store.apply_rep s291 v296 v299 _ _ hinv291 h64 h_v296 h_v299 (by ns_tac) (by ns_tac) as ⟨v300, s292, hinv292, h_v300⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 dropping h_v296 h_v299 hinv291 s291 v296 v299
  step as ⟨e_v301, he_v301⟩
  store_step with CtorSpec.eo__2d.construct s292 e_v301 (by rw [he_v301]; exact empty_args) hinv292 h64 as ⟨v301, s293, hinv293, h_v301⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 dropping he_v301 hinv292 e_v301 s292
  step as ⟨e_v302, he_v302⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s293 e_v302 (by rw [he_v302]; exact empty_args) hinv293 h64 as ⟨v302, s294, hinv294, h_v302⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 dropping he_v302 hinv293 e_v302 s293
  store_step with Store.apply_rep s294 v302 v8 _ _ hinv294 h64 h_v302 h_v8 (by ns_tac) (by ns_tac) as ⟨v303, s295, hinv295, h_v303⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 dropping h_v302 hinv294 s294 v302
  store_step with Store.apply_rep s295 v303 v5 _ _ hinv295 h64 h_v303 h_v5 (by ns_tac) (by ns_tac) as ⟨v304, s296, hinv296, h_v304⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 dropping h_v303 hinv295 s295 v303
  step as ⟨e_v305, he_v305⟩
  store_step with CtorSpec.eo__2b.construct s296 e_v305 (by rw [he_v305]; exact empty_args) hinv296 h64 as ⟨v305, s297, hinv297, h_v305⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 dropping he_v305 hinv296 e_v305 s296
  step as ⟨e_v306, he_v306⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s297 _ _ rfl hinv297 h64 as ⟨v306, s298, hinv298, h_v306⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v305 dropping hinv297 s297
  replace h_v306 := Represents.rep_of_eq h_v306 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v306]; decide)
  step as ⟨e_v307, he_v307⟩
  store_step with CtorSpec.eo_Int.construct s298 e_v307 (by rw [he_v307]; exact empty_args) hinv298 h64 as ⟨v307, s299, hinv299, h_v307⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v305 h_v306 dropping he_v306 he_v307 hinv298 e_v306 e_v307 s298
  step as ⟨e_v308, he_v308⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s299 e_v308 (by rw [he_v308]; rfl) h_v306 h_v307 hinv299 h64 as ⟨v308, s300, hinv300, h_v308⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v305 dropping h_v306 h_v307 he_v308 hinv299 e_v308 s299 v306 v307
  store_step with Store.apply_rep s300 v305 v308 _ _ hinv300 h64 h_v305 h_v308 (by ns_tac) (by ns_tac) as ⟨v309, s301, hinv301, h_v309⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 dropping h_v305 h_v308 hinv300 s300 v305 v308
  step as ⟨e_v310, he_v310⟩
  store_step with CtorSpec.eo__2b.construct s301 e_v310 (by rw [he_v310]; exact empty_args) hinv301 h64 as ⟨v310, s302, hinv302, h_v310⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v309 dropping he_v310 hinv301 e_v310 s301
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s302 1#u32 (1) (by scalar_tac) hinv302 h64 as ⟨v311, s303, hinv303, h_v311⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v309 h_v310 dropping hinv302 s302
  store_step with Store.apply_rep s303 v310 v311 _ _ hinv303 h64 h_v310 h_v311 (by ns_tac) (by ns_tac) as ⟨v312, s304, hinv304, h_v312⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v309 dropping h_v310 h_v311 hinv303 s303 v310 v311
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s304 0#u32 (0) (by scalar_tac) hinv304 h64 as ⟨v313, s305, hinv305, h_v313⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v309 h_v312 dropping hinv304 s304
  store_step with Store.apply_rep s305 v312 v313 _ _ hinv305 h64 h_v312 h_v313 (by ns_tac) (by ns_tac) as ⟨v314, s306, hinv306, h_v314⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 h_v309 dropping h_v312 h_v313 hinv305 s305 v312 v313
  store_step with Store.apply_rep s306 v309 v314 _ _ hinv306 h64 h_v309 h_v314 (by ns_tac) (by ns_tac) as ⟨v315, s307, hinv307, h_v315⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 h_v304 dropping h_v309 h_v314 hinv306 s306 v309 v314
  store_step with Store.apply_rep s307 v304 v315 _ _ hinv307 h64 h_v304 h_v315 (by ns_tac) (by ns_tac) as ⟨v316, s308, hinv308, h_v316⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v301 dropping h_v304 h_v315 hinv307 s307 v304 v315
  store_step with Store.apply_rep s308 v301 v316 _ _ hinv308 h64 h_v301 h_v316 (by ns_tac) (by ns_tac) as ⟨v317, s309, hinv309, h_v317⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 dropping h_v301 h_v316 hinv308 s308 v301 v316
  step as ⟨e_v318, he_v318⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s309 e_v318 (by rw [he_v318]; exact empty_args) hinv309 h64 as ⟨v318, s310, hinv310, h_v318⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 dropping he_v318 hinv309 e_v318 s309
  store_step with Store.apply_rep s310 v318 v8 _ _ hinv310 h64 h_v318 h_v8 (by ns_tac) (by ns_tac) as ⟨v319, s311, hinv311, h_v319⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 dropping h_v318 hinv310 s310 v318
  step as ⟨e_v320, he_v320⟩
  store_step with CtorSpec.eo_re_2ediff.construct s311 e_v320 (by rw [he_v320]; exact empty_args) hinv311 h64 as ⟨v320, s312, hinv312, h_v320⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v319 dropping he_v320 hinv311 e_v320 s311
  store_step with Store.apply_rep s312 v320 v5 _ _ hinv312 h64 h_v320 h_v5 (by ns_tac) (by ns_tac) as ⟨v321, s313, hinv313, h_v321⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v319 dropping h_v320 hinv312 s312 v320
  step as ⟨e_v322, he_v322⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s313 e_v322 (by rw [he_v322]; exact empty_args) hinv313 h64 as ⟨v322, s314, hinv314, h_v322⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v319 h_v321 dropping he_v322 hinv313 e_v322 s313
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s314 _ _ rfl hinv314 h64 as ⟨v323, s315, hinv315, h_v323⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v319 h_v321 h_v322 dropping hinv314 s314
  store_step with Store.apply_rep s315 v322 v323 _ _ hinv315 h64 h_v322 h_v323 (by ns_tac) (by ns_tac) as ⟨v324, s316, hinv316, h_v324⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v319 h_v321 dropping h_v322 h_v323 hinv315 s315 v322 v323
  store_step with Store.apply_rep s316 v321 v324 _ _ hinv316 h64 h_v321 h_v324 (by ns_tac) (by ns_tac) as ⟨v325, s317, hinv317, h_v325⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v319 dropping h_v321 h_v324 hinv316 s316 v321 v324
  store_step with Store.apply_rep s317 v319 v325 _ _ hinv317 h64 h_v319 h_v325 (by ns_tac) (by ns_tac) as ⟨v326, s318, hinv318, h_v326⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 dropping h_v319 h_v325 hinv317 s317 v319 v325
  step as ⟨e_v327, he_v327⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s318 e_v327 (by rw [he_v327]; exact empty_args) hinv318 h64 as ⟨v327, s319, hinv319, h_v327⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 dropping he_v327 hinv318 e_v327 s318
  store_step with Store.apply_rep s319 v327 v8 _ _ hinv319 h64 h_v327 h_v8 (by ns_tac) (by ns_tac) as ⟨v328, s320, hinv320, h_v328⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 dropping h_v327 hinv319 s319 v327
  store_step with Store.apply_rep s320 v328 v5 _ _ hinv320 h64 h_v328 h_v5 (by ns_tac) (by ns_tac) as ⟨v329, s321, hinv321, h_v329⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 dropping h_v328 hinv320 s320 v328
  step as ⟨e_v330, he_v330⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s321 _ _ rfl hinv321 h64 as ⟨v330, s322, hinv322, h_v330⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 h_v329 dropping hinv321 s321
  replace h_v330 := Represents.rep_of_eq h_v330 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v330]; decide)
  step as ⟨e_v331, he_v331⟩
  store_step with CtorSpec.eo_Int.construct s322 e_v331 (by rw [he_v331]; exact empty_args) hinv322 h64 as ⟨v331, s323, hinv323, h_v331⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 h_v329 h_v330 dropping he_v330 he_v331 hinv322 e_v330 e_v331 s322
  step as ⟨e_v332, he_v332⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s323 e_v332 (by rw [he_v332]; rfl) h_v330 h_v331 hinv323 h64 as ⟨v332, s324, hinv324, h_v332⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 h_v329 dropping h_v330 h_v331 he_v332 hinv323 e_v332 s323 v330 v331
  store_step with Store.apply_rep s324 v329 v332 _ _ hinv324 h64 h_v329 h_v332 (by ns_tac) (by ns_tac) as ⟨v333, s325, hinv325, h_v333⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 h_v326 dropping h_v329 h_v332 hinv324 s324 v329 v332
  store_step with Store.apply_rep s325 v326 v333 _ _ hinv325 h64 h_v326 h_v333 (by ns_tac) (by ns_tac) as ⟨v334, s326, hinv326, h_v334⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 h_v317 dropping h_v326 h_v333 hinv325 s325 v326 v333
  store_step with Store.apply_rep s326 v317 v334 _ _ hinv326 h64 h_v317 h_v334 (by ns_tac) (by ns_tac) as ⟨v335, s327, hinv327, h_v335⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 h_v300 dropping h_v317 h_v334 hinv326 s326 v317 v334
  store_step with Store.apply_rep s327 v300 v335 _ _ hinv327 h64 h_v300 h_v335 (by ns_tac) (by ns_tac) as ⟨v336, s328, hinv328, h_v336⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 h_v295 dropping h_v300 h_v335 hinv327 s327 v300 v335
  store_step with Store.apply_rep s328 v295 v336 _ _ hinv328 h64 h_v295 h_v336 (by ns_tac) (by ns_tac) as ⟨v337, s329, hinv329, h_v337⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v294 dropping h_v295 h_v336 hinv328 s328 v295 v336
  store_step with Store.apply_rep s329 v294 v337 _ _ hinv329 h64 h_v294 h_v337 (by ns_tac) (by ns_tac) as ⟨v338, s330, hinv330, h_v338⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 dropping h_v294 h_v337 hinv329 s329 v294 v337
  step as ⟨e_v339, he_v339⟩
  store_step with CtorSpec.eo_or.construct s330 e_v339 (by rw [he_v339]; exact empty_args) hinv330 h64 as ⟨v339, s331, hinv331, h_v339⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 dropping he_v339 hinv330 e_v339 s330
  step as ⟨e_v340, he_v340⟩
  store_step with CtorSpec.eo_not.construct s331 e_v340 (by rw [he_v340]; exact empty_args) hinv331 h64 as ⟨v340, s332, hinv332, h_v340⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 dropping he_v340 hinv331 e_v340 s331
  step as ⟨e_v341, he_v341⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s332 e_v341 (by rw [he_v341]; exact empty_args) hinv332 h64 as ⟨v341, s333, hinv333, h_v341⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 dropping he_v341 hinv332 e_v341 s332
  step as ⟨e_v342, he_v342⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s333 e_v342 (by rw [he_v342]; exact empty_args) hinv333 h64 as ⟨v342, s334, hinv334, h_v342⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 dropping he_v342 hinv333 e_v342 s333
  store_step with Store.apply_rep s334 v342 v8 _ _ hinv334 h64 h_v342 h_v8 (by ns_tac) (by ns_tac) as ⟨v343, s335, hinv335, h_v343⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 dropping h_v342 hinv334 s334 v342
  step as ⟨e_v344, he_v344⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s335 e_v344 (by rw [he_v344]; exact empty_args) hinv335 h64 as ⟨v344, s336, hinv336, h_v344⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 dropping he_v344 hinv335 e_v344 s335
  store_step with Store.apply_rep s336 v344 v8 _ _ hinv336 h64 h_v344 h_v8 (by ns_tac) (by ns_tac) as ⟨v345, s337, hinv337, h_v345⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 dropping h_v344 hinv336 s336 v344
  step as ⟨e_v346, he_v346⟩
  store_step with CtorSpec.eo_re_2ediff.construct s337 e_v346 (by rw [he_v346]; exact empty_args) hinv337 h64 as ⟨v346, s338, hinv338, h_v346⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v345 dropping he_v346 hinv337 e_v346 s337
  store_step with Store.apply_rep s338 v346 v5 _ _ hinv338 h64 h_v346 h_v5 (by ns_tac) (by ns_tac) as ⟨v347, s339, hinv339, h_v347⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v345 dropping h_v346 hinv338 s338 v346
  step as ⟨e_v348, he_v348⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s339 e_v348 (by rw [he_v348]; exact empty_args) hinv339 h64 as ⟨v348, s340, hinv340, h_v348⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v345 h_v347 dropping he_v348 hinv339 e_v348 s339
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s340 _ _ rfl hinv340 h64 as ⟨v349, s341, hinv341, h_v349⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v345 h_v347 h_v348 dropping hinv340 s340
  store_step with Store.apply_rep s341 v348 v349 _ _ hinv341 h64 h_v348 h_v349 (by ns_tac) (by ns_tac) as ⟨v350, s342, hinv342, h_v350⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v345 h_v347 dropping h_v348 h_v349 hinv341 s341 v348 v349
  store_step with Store.apply_rep s342 v347 v350 _ _ hinv342 h64 h_v347 h_v350 (by ns_tac) (by ns_tac) as ⟨v351, s343, hinv343, h_v351⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v345 dropping h_v347 h_v350 hinv342 s342 v347 v350
  store_step with Store.apply_rep s343 v345 v351 _ _ hinv343 h64 h_v345 h_v351 (by ns_tac) (by ns_tac) as ⟨v352, s344, hinv344, h_v352⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 dropping h_v345 h_v351 hinv343 s343 v345 v351
  step as ⟨e_v353, he_v353⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s344 e_v353 (by rw [he_v353]; exact empty_args) hinv344 h64 as ⟨v353, s345, hinv345, h_v353⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 dropping he_v353 hinv344 e_v353 s344
  store_step with Store.apply_rep s345 v353 v8 _ _ hinv345 h64 h_v353 h_v8 (by ns_tac) (by ns_tac) as ⟨v354, s346, hinv346, h_v354⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 dropping h_v353 hinv345 s345 v353
  store_step with Store.apply_rep s346 v354 v5 _ _ hinv346 h64 h_v354 h_v5 (by ns_tac) (by ns_tac) as ⟨v355, s347, hinv347, h_v355⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 dropping h_v354 hinv346 s346 v354
  step as ⟨e_v356, he_v356⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s347 _ _ rfl hinv347 h64 as ⟨v356, s348, hinv348, h_v356⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 h_v355 dropping hinv347 s347
  replace h_v356 := Represents.rep_of_eq h_v356 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v356]; decide)
  step as ⟨e_v357, he_v357⟩
  store_step with CtorSpec.eo_Int.construct s348 e_v357 (by rw [he_v357]; exact empty_args) hinv348 h64 as ⟨v357, s349, hinv349, h_v357⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 h_v355 h_v356 dropping he_v356 he_v357 hinv348 e_v356 e_v357 s348
  step as ⟨e_v358, he_v358⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s349 e_v358 (by rw [he_v358]; rfl) h_v356 h_v357 hinv349 h64 as ⟨v358, s350, hinv350, h_v358⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 h_v355 dropping h_v356 h_v357 he_v358 hinv349 e_v358 s349 v356 v357
  store_step with Store.apply_rep s350 v355 v358 _ _ hinv350 h64 h_v355 h_v358 (by ns_tac) (by ns_tac) as ⟨v359, s351, hinv351, h_v359⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 h_v352 dropping h_v355 h_v358 hinv350 s350 v355 v358
  store_step with Store.apply_rep s351 v352 v359 _ _ hinv351 h64 h_v352 h_v359 (by ns_tac) (by ns_tac) as ⟨v360, s352, hinv352, h_v360⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v343 dropping h_v352 h_v359 hinv351 s351 v352 v359
  store_step with Store.apply_rep s352 v343 v360 _ _ hinv352 h64 h_v343 h_v360 (by ns_tac) (by ns_tac) as ⟨v361, s353, hinv353, h_v361⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 dropping h_v343 h_v360 hinv352 s352 v343 v360
  step as ⟨e_v362, he_v362⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s353 _ _ rfl hinv353 h64 as ⟨v362, s354, hinv354, h_v362⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v361 dropping hinv353 s353
  replace h_v362 := Represents.rep_of_eq h_v362 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_length")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v362]; decide)
  step as ⟨e_v363, he_v363⟩
  store_step with CtorSpec.eo_Int.construct s354 e_v363 (by rw [he_v363]; exact empty_args) hinv354 h64 as ⟨v363, s355, hinv355, h_v363⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v361 h_v362 dropping he_v362 he_v363 hinv354 e_v362 e_v363 s354
  step as ⟨e_v364, he_v364⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s355 e_v364 (by rw [he_v364]; rfl) h_v362 h_v363 hinv355 h64 as ⟨v364, s356, hinv356, h_v364⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 h_v361 dropping h_v362 h_v363 he_v364 hinv355 e_v364 s355 v362 v363
  store_step with Store.apply_rep s356 v361 v364 _ _ hinv356 h64 h_v361 h_v364 (by ns_tac) (by ns_tac) as ⟨v365, s357, hinv357, h_v365⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 h_v341 dropping h_v361 h_v364 hinv356 s356 v361 v364
  store_step with Store.apply_rep s357 v341 v365 _ _ hinv357 h64 h_v341 h_v365 (by ns_tac) (by ns_tac) as ⟨v366, s358, hinv358, h_v366⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 dropping h_v341 h_v365 hinv357 s357 v341 v365
  store_step with Store.apply_rep s358 v366 v5 _ _ hinv358 h64 h_v366 h_v5 (by ns_tac) (by ns_tac) as ⟨v367, s359, hinv359, h_v367⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 h_v340 dropping h_v366 hinv358 s358 v366
  store_step with Store.apply_rep s359 v340 v367 _ _ hinv359 h64 h_v340 h_v367 (by ns_tac) (by ns_tac) as ⟨v368, s360, hinv360, h_v368⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v339 dropping h_v340 h_v367 hinv359 s359 v340 v367
  store_step with Store.apply_rep s360 v339 v368 _ _ hinv360 h64 h_v339 h_v368 (by ns_tac) (by ns_tac) as ⟨v369, s361, hinv361, h_v369⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 dropping h_v339 h_v368 hinv360 s360 v339 v368
  store_step with Store.literal_boolean_spec s361 false hinv361 h64 as ⟨v370, s362, hinv362, h_v370⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 h_v369 dropping hinv361 s361
  store_step with Store.apply_rep s362 v369 v370 _ _ hinv362 h64 h_v369 h_v370 (by ns_tac) (by ns_tac) as ⟨v371, s363, hinv363, h_v371⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 h_v338 dropping h_v369 h_v370 hinv362 s362 v369 v370
  store_step with Store.apply_rep s363 v338 v371 _ _ hinv363 h64 h_v338 h_v371 (by ns_tac) (by ns_tac) as ⟨v372, s364, hinv364, h_v372⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 h_v293 dropping h_v338 h_v371 hinv363 s363 v338 v371
  store_step with Store.apply_rep s364 v293 v372 _ _ hinv364 h64 h_v293 h_v372 (by ns_tac) (by ns_tac) as ⟨v373, s365, hinv365, h_v373⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 h_v282 dropping h_v293 h_v372 hinv364 s364 v293 v372
  store_step with Store.apply_rep s365 v282 v373 _ _ hinv365 h64 h_v282 h_v373 (by ns_tac) (by ns_tac) as ⟨v374, s366, hinv366, h_v374⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v273 dropping h_v282 h_v373 hinv365 s365 v282 v373
  store_step with Store.apply_rep s366 v273 v374 _ _ hinv366 h64 h_v273 h_v374 (by ns_tac) (by ns_tac) as ⟨v375, s367, hinv367, h_v375⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 dropping h_v273 h_v374 hinv366 s366 v273 v374
  step as ⟨e_v376, he_v376⟩
  store_step with CtorSpec.eo_and.construct s367 e_v376 (by rw [he_v376]; exact empty_args) hinv367 h64 as ⟨v376, s368, hinv368, h_v376⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 dropping he_v376 hinv367 e_v376 s367
  step as ⟨e_v377, he_v377⟩
  store_step with CtorSpec.eo__3d.construct s368 e_v377 (by rw [he_v377]; exact empty_args) hinv368 h64 as ⟨v377, s369, hinv369, h_v377⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 dropping he_v377 hinv368 e_v377 s368
  step as ⟨e_v378, he_v378⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct s369 e_v378 (by rw [he_v378]; exact empty_args) hinv369 h64 as ⟨v378, s370, hinv370, h_v378⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 dropping he_v378 hinv369 e_v378 s369
  store_step with Store.apply_rep s370 v378 v8 _ _ hinv370 h64 h_v378 h_v8 (by ns_tac) (by ns_tac) as ⟨v379, s371, hinv371, h_v379⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 dropping h_v378 hinv370 s370 v378
  store_step with Store.apply_rep s371 v379 v5 _ _ hinv371 h64 h_v379 h_v5 (by ns_tac) (by ns_tac) as ⟨v380, s372, hinv372, h_v380⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 dropping h_v379 hinv371 s371 v379
  store_step with Store.apply_rep s372 v380 v2 _ _ hinv372 h64 h_v380 h_v2 (by ns_tac) (by ns_tac) as ⟨v381, s373, hinv373, h_v381⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 dropping h_v380 hinv372 s372 v380
  step as ⟨e_v382, he_v382⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s373 _ _ rfl hinv373 h64 as ⟨v382, s374, hinv374, h_v382⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 h_v381 dropping hinv373 s373
  replace h_v382 := Represents.rep_of_eq h_v382 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v382]; decide)
  step as ⟨e_v383, he_v383⟩
  store_step with CtorSpec.eo_Int.construct s374 e_v383 (by rw [he_v383]; exact empty_args) hinv374 h64 as ⟨v383, s375, hinv375, h_v383⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 h_v381 h_v382 dropping he_v382 he_v383 hinv374 e_v382 e_v383 s374
  step as ⟨e_v384, he_v384⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s375 e_v384 (by rw [he_v384]; rfl) h_v382 h_v383 hinv375 h64 as ⟨v384, s376, hinv376, h_v384⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 h_v381 dropping h_v382 h_v383 he_v384 hinv375 e_v384 s375 v382 v383
  store_step with Store.apply_rep s376 v381 v384 _ _ hinv376 h64 h_v381 h_v384 (by ns_tac) (by ns_tac) as ⟨v385, s377, hinv377, h_v385⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v377 dropping h_v381 h_v384 hinv376 s376 v381 v384
  store_step with Store.apply_rep s377 v377 v385 _ _ hinv377 h64 h_v377 h_v385 (by ns_tac) (by ns_tac) as ⟨v386, s378, hinv378, h_v386⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 dropping h_v377 h_v385 hinv377 s377 v377 v385
  step as ⟨e_v387, he_v387⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s378 e_v387 (by rw [he_v387]; exact empty_args) hinv378 h64 as ⟨v387, s379, hinv379, h_v387⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 dropping he_v387 hinv378 e_v387 s378
  step as ⟨e_v388, he_v388⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s379 e_v388 (by rw [he_v388]; exact empty_args) hinv379 h64 as ⟨v388, s380, hinv380, h_v388⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 dropping he_v388 hinv379 e_v388 s379
  store_step with Store.apply_rep s380 v388 v8 _ _ hinv380 h64 h_v388 h_v8 (by ns_tac) (by ns_tac) as ⟨v389, s381, hinv381, h_v389⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 dropping h_v388 hinv380 s380 v388
  step as ⟨e_v390, he_v390⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s381 e_v390 (by rw [he_v390]; exact empty_args) hinv381 h64 as ⟨v390, s382, hinv382, h_v390⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 dropping he_v390 hinv381 e_v390 s381
  store_step with Store.apply_rep s382 v390 v8 _ _ hinv382 h64 h_v390 h_v8 (by ns_tac) (by ns_tac) as ⟨v391, s383, hinv383, h_v391⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 dropping h_v390 hinv382 s382 v390
  store_step with Store.apply_rep s383 v391 v5 _ _ hinv383 h64 h_v391 h_v5 (by ns_tac) (by ns_tac) as ⟨v392, s384, hinv384, h_v392⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 dropping h_v391 hinv383 s383 v391
  step as ⟨e_v393, he_v393⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s384 _ _ rfl hinv384 h64 as ⟨v393, s385, hinv385, h_v393⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 h_v392 dropping hinv384 s384
  replace h_v393 := Represents.rep_of_eq h_v393 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v393]; decide)
  step as ⟨e_v394, he_v394⟩
  store_step with CtorSpec.eo_Int.construct s385 e_v394 (by rw [he_v394]; exact empty_args) hinv385 h64 as ⟨v394, s386, hinv386, h_v394⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 h_v392 h_v393 dropping he_v393 he_v394 hinv385 e_v393 e_v394 s385
  step as ⟨e_v395, he_v395⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s386 e_v395 (by rw [he_v395]; rfl) h_v393 h_v394 hinv386 h64 as ⟨v395, s387, hinv387, h_v395⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 h_v392 dropping h_v393 h_v394 he_v395 hinv386 e_v395 s386 v393 v394
  store_step with Store.apply_rep s387 v392 v395 _ _ hinv387 h64 h_v392 h_v395 (by ns_tac) (by ns_tac) as ⟨v396, s388, hinv388, h_v396⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v389 dropping h_v392 h_v395 hinv387 s387 v392 v395
  store_step with Store.apply_rep s388 v389 v396 _ _ hinv388 h64 h_v389 h_v396 (by ns_tac) (by ns_tac) as ⟨v397, s389, hinv389, h_v397⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 dropping h_v389 h_v396 hinv388 s388 v389 v396
  step as ⟨e_v398, he_v398⟩
  store_step with CtorSpec.eo__2d.construct s389 e_v398 (by rw [he_v398]; exact empty_args) hinv389 h64 as ⟨v398, s390, hinv390, h_v398⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 dropping he_v398 hinv389 e_v398 s389
  step as ⟨e_v399, he_v399⟩
  store_step with CtorSpec.eo_str_2eindexof_5fre.construct s390 e_v399 (by rw [he_v399]; exact empty_args) hinv390 h64 as ⟨v399, s391, hinv391, h_v399⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 dropping he_v399 hinv390 e_v399 s390
  store_step with Store.apply_rep s391 v399 v8 _ _ hinv391 h64 h_v399 h_v8 (by ns_tac) (by ns_tac) as ⟨v400, s392, hinv392, h_v400⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 dropping h_v399 hinv391 s391 v399
  step as ⟨e_v401, he_v401⟩
  store_step with CtorSpec.eo_re_2ediff.construct s392 e_v401 (by rw [he_v401]; exact empty_args) hinv392 h64 as ⟨v401, s393, hinv393, h_v401⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v400 dropping he_v401 hinv392 e_v401 s392
  store_step with Store.apply_rep s393 v401 v5 _ _ hinv393 h64 h_v401 h_v5 (by ns_tac) (by ns_tac) as ⟨v402, s394, hinv394, h_v402⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v400 dropping h_v401 hinv393 s393 v401
  step as ⟨e_v403, he_v403⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s394 e_v403 (by rw [he_v403]; exact empty_args) hinv394 h64 as ⟨v403, s395, hinv395, h_v403⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v400 h_v402 dropping he_v403 hinv394 e_v403 s394
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s395 _ _ rfl hinv395 h64 as ⟨v404, s396, hinv396, h_v404⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v400 h_v402 h_v403 dropping hinv395 s395
  store_step with Store.apply_rep s396 v403 v404 _ _ hinv396 h64 h_v403 h_v404 (by ns_tac) (by ns_tac) as ⟨v405, s397, hinv397, h_v405⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v400 h_v402 dropping h_v403 h_v404 hinv396 s396 v403 v404
  store_step with Store.apply_rep s397 v402 v405 _ _ hinv397 h64 h_v402 h_v405 (by ns_tac) (by ns_tac) as ⟨v406, s398, hinv398, h_v406⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v400 dropping h_v402 h_v405 hinv397 s397 v402 v405
  store_step with Store.apply_rep s398 v400 v406 _ _ hinv398 h64 h_v400 h_v406 (by ns_tac) (by ns_tac) as ⟨v407, s399, hinv399, h_v407⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 dropping h_v400 h_v406 hinv398 s398 v400 v406
  step as ⟨e_v408, he_v408⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s399 e_v408 (by rw [he_v408]; exact empty_args) hinv399 h64 as ⟨v408, s400, hinv400, h_v408⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 dropping he_v408 hinv399 e_v408 s399
  store_step with Store.apply_rep s400 v408 v8 _ _ hinv400 h64 h_v408 h_v8 (by ns_tac) (by ns_tac) as ⟨v409, s401, hinv401, h_v409⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 dropping h_v408 hinv400 s400 v408
  store_step with Store.apply_rep s401 v409 v5 _ _ hinv401 h64 h_v409 h_v5 (by ns_tac) (by ns_tac) as ⟨v410, s402, hinv402, h_v410⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 dropping h_v409 hinv401 s401 v409
  step as ⟨e_v411, he_v411⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s402 _ _ rfl hinv402 h64 as ⟨v411, s403, hinv403, h_v411⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 h_v410 dropping hinv402 s402
  replace h_v411 := Represents.rep_of_eq h_v411 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v411]; decide)
  step as ⟨e_v412, he_v412⟩
  store_step with CtorSpec.eo_Int.construct s403 e_v412 (by rw [he_v412]; exact empty_args) hinv403 h64 as ⟨v412, s404, hinv404, h_v412⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 h_v410 h_v411 dropping he_v411 he_v412 hinv403 e_v411 e_v412 s403
  step as ⟨e_v413, he_v413⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s404 e_v413 (by rw [he_v413]; rfl) h_v411 h_v412 hinv404 h64 as ⟨v413, s405, hinv405, h_v413⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 h_v410 dropping h_v411 h_v412 he_v413 hinv404 e_v413 s404 v411 v412
  store_step with Store.apply_rep s405 v410 v413 _ _ hinv405 h64 h_v410 h_v413 (by ns_tac) (by ns_tac) as ⟨v414, s406, hinv406, h_v414⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 h_v407 dropping h_v410 h_v413 hinv405 s405 v410 v413
  store_step with Store.apply_rep s406 v407 v414 _ _ hinv406 h64 h_v407 h_v414 (by ns_tac) (by ns_tac) as ⟨v415, s407, hinv407, h_v415⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v398 dropping h_v407 h_v414 hinv406 s406 v407 v414
  store_step with Store.apply_rep s407 v398 v415 _ _ hinv407 h64 h_v398 h_v415 (by ns_tac) (by ns_tac) as ⟨v416, s408, hinv408, h_v416⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 dropping h_v398 h_v415 hinv407 s407 v398 v415
  step as ⟨e_v417, he_v417⟩
  store_step with CtorSpec.eo__40strings_5foccur_5findex_5fre.construct s408 e_v417 (by rw [he_v417]; exact empty_args) hinv408 h64 as ⟨v417, s409, hinv409, h_v417⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 dropping he_v417 hinv408 e_v417 s408
  store_step with Store.apply_rep s409 v417 v8 _ _ hinv409 h64 h_v417 h_v8 (by ns_tac) (by ns_tac) as ⟨v418, s410, hinv410, h_v418⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 dropping h_v417 hinv409 s409 v417
  store_step with Store.apply_rep s410 v418 v5 _ _ hinv410 h64 h_v418 h_v5 (by ns_tac) (by ns_tac) as ⟨v419, s411, hinv411, h_v419⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 dropping h_v418 hinv410 s410 v418
  step as ⟨e_v420, he_v420⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s411 _ _ rfl hinv411 h64 as ⟨v420, s412, hinv412, h_v420⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 h_v419 dropping hinv411 s411
  replace h_v420 := Represents.rep_of_eq h_v420 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v420]; decide)
  step as ⟨e_v421, he_v421⟩
  store_step with CtorSpec.eo_Int.construct s412 e_v421 (by rw [he_v421]; exact empty_args) hinv412 h64 as ⟨v421, s413, hinv413, h_v421⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 h_v419 h_v420 dropping he_v420 he_v421 hinv412 e_v420 e_v421 s412
  step as ⟨e_v422, he_v422⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s413 e_v422 (by rw [he_v422]; rfl) h_v420 h_v421 hinv413 h64 as ⟨v422, s414, hinv414, h_v422⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 h_v419 dropping h_v420 h_v421 he_v422 hinv413 e_v422 s413 v420 v421
  store_step with Store.apply_rep s414 v419 v422 _ _ hinv414 h64 h_v419 h_v422 (by ns_tac) (by ns_tac) as ⟨v423, s415, hinv415, h_v423⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 h_v416 dropping h_v419 h_v422 hinv414 s414 v419 v422
  store_step with Store.apply_rep s415 v416 v423 _ _ hinv415 h64 h_v416 h_v423 (by ns_tac) (by ns_tac) as ⟨v424, s416, hinv416, h_v424⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 h_v397 dropping h_v416 h_v423 hinv415 s415 v416 v423
  store_step with Store.apply_rep s416 v397 v424 _ _ hinv416 h64 h_v397 h_v424 (by ns_tac) (by ns_tac) as ⟨v425, s417, hinv417, h_v425⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v387 dropping h_v397 h_v424 hinv416 s416 v397 v424
  store_step with Store.apply_rep s417 v387 v425 _ _ hinv417 h64 h_v387 h_v425 (by ns_tac) (by ns_tac) as ⟨v426, s418, hinv418, h_v426⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 dropping h_v387 h_v425 hinv417 s417 v387 v425
  step as ⟨e_v427, he_v427⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s418 e_v427 (by rw [he_v427]; exact empty_args) hinv418 h64 as ⟨v427, s419, hinv419, h_v427⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 dropping he_v427 hinv418 e_v427 s418
  store_step with Store.apply_rep s419 v427 v2 _ _ hinv419 h64 h_v427 h_v2 (by ns_tac) (by ns_tac) as ⟨v428, s420, hinv420, h_v428⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 dropping h_v427 hinv419 s419 v427
  step as ⟨e_v429, he_v429⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s420 e_v429 (by rw [he_v429]; exact empty_args) hinv420 h64 as ⟨v429, s421, hinv421, h_v429⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 dropping he_v429 hinv420 e_v429 s420
  step as ⟨e_v430, he_v430⟩
  store_step with CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct s421 e_v430 (by rw [he_v430]; exact empty_args) hinv421 h64 as ⟨v430, s422, hinv422, h_v430⟩ growing hG carrying h_v2 h_v5 h_v8 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 dropping he_v430 hinv421 e_v430 s421
  store_step with Store.apply_rep s422 v430 v8 _ _ hinv422 h64 h_v430 h_v8 (by ns_tac) (by ns_tac) as ⟨v431, s423, hinv423, h_v431⟩ growing hG carrying h_v2 h_v5 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 dropping h_v430 h_v8 hinv422 s422 v430 v8
  store_step with Store.apply_rep s423 v431 v5 _ _ hinv423 h64 h_v431 h_v5 (by ns_tac) (by ns_tac) as ⟨v432, s424, hinv424, h_v432⟩ growing hG carrying h_v2 h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 dropping h_v431 h_v5 hinv423 s423 v431 v5
  store_step with Store.apply_rep s424 v432 v2 _ _ hinv424 h64 h_v432 h_v2 (by ns_tac) (by ns_tac) as ⟨v433, s425, hinv425, h_v433⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 dropping h_v2 h_v432 hinv424 s424 v2 v432
  step as ⟨e_v434, he_v434⟩
  store_step with CtorSpec.eo__2b.construct s425 e_v434 (by rw [he_v434]; exact empty_args) hinv425 h64 as ⟨v434, s426, hinv426, h_v434⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 dropping he_v434 hinv425 e_v434 s425
  step as ⟨e_v435, he_v435⟩
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s426 _ _ rfl hinv426 h64 as ⟨v435, s427, hinv427, h_v435⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v434 dropping hinv426 s426
  replace h_v435 := Represents.rep_of_eq h_v435 (y := Eo.Term.String (SmtEval.native_string_lit "@var.str_index")) (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val, he_v435]; decide)
  step as ⟨e_v436, he_v436⟩
  store_step with CtorSpec.eo_Int.construct s427 e_v436 (by rw [he_v436]; exact empty_args) hinv427 h64 as ⟨v436, s428, hinv428, h_v436⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v434 h_v435 dropping he_v435 he_v436 hinv427 e_v435 e_v436 s427
  step as ⟨e_v437, he_v437⟩
  store_step with CtorSpec.eo__24emb_5fVar.construct s428 e_v437 (by rw [he_v437]; rfl) h_v435 h_v436 hinv428 h64 as ⟨v437, s429, hinv429, h_v437⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v434 dropping h_v435 h_v436 he_v437 hinv428 e_v437 s428 v435 v436
  store_step with Store.apply_rep s429 v434 v437 _ _ hinv429 h64 h_v434 h_v437 (by ns_tac) (by ns_tac) as ⟨v438, s430, hinv430, h_v438⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 dropping h_v434 h_v437 hinv429 s429 v434 v437
  step as ⟨e_v439, he_v439⟩
  store_step with CtorSpec.eo__2b.construct s430 e_v439 (by rw [he_v439]; exact empty_args) hinv430 h64 as ⟨v439, s431, hinv431, h_v439⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v438 dropping he_v439 hinv430 e_v439 s430
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s431 1#u32 (1) (by scalar_tac) hinv431 h64 as ⟨v440, s432, hinv432, h_v440⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v438 h_v439 dropping hinv431 s431
  store_step with Store.apply_rep s432 v439 v440 _ _ hinv432 h64 h_v439 h_v440 (by ns_tac) (by ns_tac) as ⟨v441, s433, hinv433, h_v441⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v438 dropping h_v439 h_v440 hinv432 s432 v439 v440
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s433 0#u32 (0) (by scalar_tac) hinv433 h64 as ⟨v442, s434, hinv434, h_v442⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v438 h_v441 dropping hinv433 s433
  store_step with Store.apply_rep s434 v441 v442 _ _ hinv434 h64 h_v441 h_v442 (by ns_tac) (by ns_tac) as ⟨v443, s435, hinv435, h_v443⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 h_v438 dropping h_v441 h_v442 hinv434 s434 v441 v442
  store_step with Store.apply_rep s435 v438 v443 _ _ hinv435 h64 h_v438 h_v443 (by ns_tac) (by ns_tac) as ⟨v444, s436, hinv436, h_v444⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 h_v433 dropping h_v438 h_v443 hinv435 s435 v438 v443
  store_step with Store.apply_rep s436 v433 v444 _ _ hinv436 h64 h_v433 h_v444 (by ns_tac) (by ns_tac) as ⟨v445, s437, hinv437, h_v445⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v429 dropping h_v433 h_v444 hinv436 s436 v433 v444
  store_step with Store.apply_rep s437 v429 v445 _ _ hinv437 h64 h_v429 h_v445 (by ns_tac) (by ns_tac) as ⟨v446, s438, hinv438, h_v446⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 dropping h_v429 h_v445 hinv437 s437 v429 v445
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s438 _ _ rfl hinv438 h64 as ⟨v447, s439, hinv439, h_v447⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 h_v446 dropping hinv438 s438
  store_step with Store.apply_rep s439 v446 v447 _ _ hinv439 h64 h_v446 h_v447 (by ns_tac) (by ns_tac) as ⟨v448, s440, hinv440, h_v448⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 h_v428 dropping h_v446 h_v447 hinv439 s439 v446 v447
  store_step with Store.apply_rep s440 v428 v448 _ _ hinv440 h64 h_v428 h_v448 (by ns_tac) (by ns_tac) as ⟨v449, s441, hinv441, h_v449⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 h_v426 dropping h_v428 h_v448 hinv440 s440 v428 v448
  store_step with Store.apply_rep s441 v426 v449 _ _ hinv441 h64 h_v426 h_v449 (by ns_tac) (by ns_tac) as ⟨v450, s442, hinv442, h_v450⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 h_v386 dropping h_v426 h_v449 hinv441 s441 v426 v449
  store_step with Store.apply_rep s442 v386 v450 _ _ hinv442 h64 h_v386 h_v450 (by ns_tac) (by ns_tac) as ⟨v451, s443, hinv443, h_v451⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v376 dropping h_v386 h_v450 hinv442 s442 v386 v450
  store_step with Store.apply_rep s443 v376 v451 _ _ hinv443 h64 h_v376 h_v451 (by ns_tac) (by ns_tac) as ⟨v452, s444, hinv444, h_v452⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 dropping h_v376 h_v451 hinv443 s443 v376 v451
  store_step with Store.literal_boolean_spec s444 true hinv444 h64 as ⟨v453, s445, hinv445, h_v453⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 h_v452 dropping hinv444 s444
  store_step with Store.apply_rep s445 v452 v453 _ _ hinv445 h64 h_v452 h_v453 (by ns_tac) (by ns_tac) as ⟨v454, s446, hinv446, h_v454⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 h_v375 dropping h_v452 h_v453 hinv445 s445 v452 v453
  store_step with Store.apply_rep s446 v375 v454 _ _ hinv446 h64 h_v375 h_v454 (by ns_tac) (by ns_tac) as ⟨v455, s447, hinv447, h_v455⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 h_v272 dropping h_v375 h_v454 hinv446 s446 v375 v454
  store_step with Store.apply_rep s447 v272 v455 _ _ hinv447 h64 h_v272 h_v455 (by ns_tac) (by ns_tac) as ⟨v456, s448, hinv448, h_v456⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 h_v205 dropping h_v272 h_v455 hinv447 s447 v272 v455
  store_step with Store.apply_rep s448 v205 v456 _ _ hinv448 h64 h_v205 h_v456 (by ns_tac) (by ns_tac) as ⟨v457, s449, hinv449, h_v457⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v164 dropping h_v205 h_v456 hinv448 s448 v205 v456
  store_step with Store.apply_rep s449 v164 v457 _ _ hinv449 h64 h_v164 h_v457 (by ns_tac) (by ns_tac) as ⟨v458, s450, hinv450, h_v458⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 dropping h_v164 h_v457 hinv449 s449 v164 v457
  store_step with Store.literal_boolean_spec s450 false hinv450 h64 as ⟨v459, s451, hinv451, h_v459⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 h_v458 dropping hinv450 s450
  store_step with Store.apply_rep s451 v458 v459 _ _ hinv451 h64 h_v458 h_v459 (by ns_tac) (by ns_tac) as ⟨v460, s452, hinv452, h_v460⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 h_v163 dropping h_v458 h_v459 hinv451 s451 v458 v459
  store_step with Store.apply_rep s452 v163 v460 _ _ hinv452 h64 h_v163 h_v460 (by ns_tac) (by ns_tac) as ⟨v461, s453, hinv453, h_v461⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 h_v150 dropping h_v163 h_v460 hinv452 s452 v163 v460
  store_step with Store.apply_rep s453 v150 v461 _ _ hinv453 h64 h_v150 h_v461 (by ns_tac) (by ns_tac) as ⟨v462, s454, hinv454, h_v462⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 h_v139 dropping h_v150 h_v461 hinv453 s453 v150 v461
  store_step with Store.apply_rep s454 v139 v462 _ _ hinv454 h64 h_v139 h_v462 (by ns_tac) (by ns_tac) as ⟨v463, s455, hinv455, h_v463⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v130 dropping h_v139 h_v462 hinv454 s454 v139 v462
  store_step with Store.apply_rep s455 v130 v463 _ _ hinv455 h64 h_v130 h_v463 (by ns_tac) (by ns_tac) as ⟨v464, s456, hinv456, h_v464⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 dropping h_v130 h_v463 hinv455 s455 v130 v463
  store_step with Store.literal_boolean_spec s456 true hinv456 h64 as ⟨v465, s457, hinv457, h_v465⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 h_v464 dropping hinv456 s456
  store_step with Store.apply_rep s457 v464 v465 _ _ hinv457 h64 h_v464 h_v465 (by ns_tac) (by ns_tac) as ⟨v466, s458, hinv458, h_v466⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 h_v129 dropping h_v464 h_v465 hinv457 s457 v464 v465
  store_step with Store.apply_rep s458 v129 v466 _ _ hinv458 h64 h_v129 h_v466 (by ns_tac) (by ns_tac) as ⟨v467, s459, hinv459, h_v467⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 h_v99 dropping h_v129 h_v466 hinv458 s458 v129 v466
  store_step with Store.apply_rep s459 v99 v467 _ _ hinv459 h64 h_v99 h_v467 (by ns_tac) (by ns_tac) as ⟨v468, s460, hinv460, h_v468⟩ growing hG carrying h_v36 h_v45 h_v62 h_v88 dropping h_v467 h_v99 hinv459 s459 v467 v99
  store_step with Store.apply_rep s460 v88 v468 _ _ hinv460 h64 h_v88 h_v468 (by ns_tac) (by ns_tac) as ⟨v469, s461, hinv461, h_v469⟩ growing hG carrying h_v36 h_v45 h_v62 dropping h_v468 h_v88 hinv460 s460 v468 v88
  store_step with Store.apply_rep s461 v62 v469 _ _ hinv461 h64 h_v62 h_v469 (by ns_tac) (by ns_tac) as ⟨v470, s462, hinv462, h_v470⟩ growing hG carrying h_v36 h_v45 dropping h_v469 h_v62 hinv461 s461 v469 v62
  store_step with Store.apply_rep s462 v45 v470 _ _ hinv462 h64 h_v45 h_v470 (by ns_tac) (by ns_tac) as ⟨v471, s463, hinv463, h_v471⟩ growing hG carrying h_v36 dropping h_v45 h_v470 hinv462 s462 v45 v470
  store_step with Store.apply_rep s463 v36 v471 _ _ hinv463 h64 h_v36 h_v471 (by ns_tac) (by ns_tac) as ⟨v472, s464, hinv464, h_v472⟩ growing hG carrying dropping h_v36 h_v471 hinv463 s463 v36 v471
  case_done hinv464 hG with h_v472 in EoCases.__str_reduction_pred.case_10 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v7 hn_v8

end pathos_compiled_checker
