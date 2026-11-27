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

set_option maxHeartbeats 5000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dumulo_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dumulo_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_umulo_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_umulo_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dumulo_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_umulo_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_umulo_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_umulo_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_umulo_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_umulo_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_bvumulo.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_umulo_elim.case_0
  store_step with ih.eo__24eo_5ftypeof s2 v12 _ hinv2 h64 (hG.rem hrem) h_v12 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  store_step with ih.eo__24bv_5fbitwidth s3 v14 _ hinv3 h64 (hG.rem hrem) h_v14 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 hinv3 s3 v14
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 h_v15 dropping hinv4 s4
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_eq s5 e_v17 (by rw [he_v17]; rfl) h_v15 h_v16 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v15 h_v16 he_v17 hinv5 e_v17 s5 v15 v16
  have h_ite_v144 := (show if_11_eo__24eo_5fprog_5fbv_2dumulo_2delim s6 v17 v12 v9 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_11_eo__24eo_5fprog_5fbv_2dumulo_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
    · ite_branch hbv_18
      store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v17 v17
      ite_done hinv7 hG with (eo_ite_true_rep _ hx_18 h_v18)
    · ite_branch hbv_18
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo__3d.construct s6 e_v19 (by rw [he_v19]; exact empty_args) hinv6 h64 as ⟨v19, s7, hinv7, h_v19⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v17 he_v19 e_v19 v17
      store_step with ih.eo__24eo_5ftypeof s7 v12 _ hinv7 h64 (hG.rem hrem) h_v12 as ⟨v20, s8, hinv8, h_v20⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 dropping
      store_step with ih.eo__24bv_5fbitwidth s8 v20 _ hinv8 h64 (hG.rem hrem) h_v20 as ⟨v21, s9, hinv9, h_v21⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 dropping h_v20 v20
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s9 1#u32 (-1) (by scalar_tac) hinv9 h64 as ⟨v22, s10, hinv10, h_v22⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v21 dropping
      step as ⟨e_v23, he_v23⟩
      store_step with Store.builtin_spec_add s10 e_v23 (by rw [he_v23]; rfl) h_v21 h_v22 hinv10 h64 as ⟨v23, s11, hinv11, h_v23⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 dropping h_v21 h_v22 he_v23 e_v23 v21 v22
      store_step with ih.eo__24eo_5ftypeof s11 v12 _ hinv11 h64 (hG.rem hrem) h_v12 as ⟨v24, s12, hinv12, h_v24⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v23 dropping
      store_step with ih.eo__24bv_5fbitwidth s12 v24 _ hinv12 h64 (hG.rem hrem) h_v24 as ⟨v25, s13, hinv13, h_v25⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v23 dropping h_v24 v24
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s13 1#u32 (-1) (by scalar_tac) hinv13 h64 as ⟨v26, s14, hinv14, h_v26⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v23 h_v25 dropping
      step as ⟨e_v27, he_v27⟩
      store_step with Store.builtin_spec_add s14 e_v27 (by rw [he_v27]; rfl) h_v25 h_v26 hinv14 h64 as ⟨v27, s15, hinv15, h_v27⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v23 dropping h_v25 h_v26 he_v27 e_v27 v25 v26
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_extract.construct s15 e_v28 (by rw [he_v28]; rfl) h_v23 h_v27 hinv15 h64 as ⟨v28, s16, hinv16, h_v28⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 dropping h_v23 h_v27 he_v28 hinv15 e_v28 s15 v23 v27
      store_step with Store.apply_mk_rep s16 v28 v12 _ _ hinv16 h64 h_v28 h_v12 as ⟨v29, s17, hinv17, h_v29⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 dropping h_v28 hinv16 s16 v28
      step as ⟨e_v30, he_v30⟩
      store_step with CtorSpec.eo_bvor.construct s17 e_v30 (by rw [he_v30]; exact empty_args) hinv17 h64 as ⟨v30, s18, hinv18, h_v30⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 dropping he_v30 hinv17 e_v30 s17
      store_step with ih.eo__24eo_5ftypeof s18 v12 _ hinv18 h64 (hG.rem hrem) h_v12 as ⟨v31, s19, hinv19, h_v31⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 dropping hinv18 s18
      store_step with ih.eo__24bv_5fbitwidth s19 v31 _ hinv19 h64 (hG.rem hrem) h_v31 as ⟨v32, s20, hinv20, h_v32⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 dropping h_v31 hinv19 s19 v31
      store_step with ih.eo__24eo_5ftypeof s20 v12 _ hinv20 h64 (hG.rem hrem) h_v12 as ⟨v33, s21, hinv21, h_v33⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v32 dropping hinv20 s20
      store_step with ih.eo__24bv_5fbitwidth s21 v33 _ hinv21 h64 (hG.rem hrem) h_v33 as ⟨v34, s22, hinv22, h_v34⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v32 dropping h_v33 hinv21 s21 v33
      step as ⟨e_v35, he_v35⟩
      store_step with CtorSpec.eo_extract.construct s22 e_v35 (by rw [he_v35]; rfl) h_v32 h_v34 hinv22 h64 as ⟨v35, s23, hinv23, h_v35⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 dropping h_v32 h_v34 he_v35 hinv22 e_v35 s22 v32 v34
      step as ⟨e_v36, he_v36⟩
      store_step with CtorSpec.eo_bvmul.construct s23 e_v36 (by rw [he_v36]; exact empty_args) hinv23 h64 as ⟨v36, s24, hinv24, h_v36⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 dropping he_v36 hinv23 e_v36 s23
      step as ⟨e_v37, he_v37⟩
      store_step with CtorSpec.eo_concat.construct s24 e_v37 (by rw [he_v37]; exact empty_args) hinv24 h64 as ⟨v37, s25, hinv25, h_v37⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 dropping he_v37 hinv24 e_v37 s24
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s25 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv25 h64 as ⟨v38, s26, hinv26, h_v38⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 h_v37 dropping hinv25 s25
      store_step with Store.apply_rep s26 v37 v38 _ _ hinv26 h64 h_v37 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s27, hinv27, h_v39⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 dropping h_v37 h_v38 hinv26 s26 v37 v38
      step as ⟨e_v40, he_v40⟩
      store_step with CtorSpec.eo_concat.construct s27 e_v40 (by rw [he_v40]; exact empty_args) hinv27 h64 as ⟨v40, s28, hinv28, h_v40⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 h_v39 dropping he_v40 hinv27 e_v40 s27
      store_step with Store.apply_rep s28 v40 v12 _ _ hinv28 h64 h_v40 h_v12 (by ns_tac) (by ns_tac) as ⟨v41, s29, hinv29, h_v41⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 h_v39 dropping h_v40 hinv28 s28 v40
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s29 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv29 h64 as ⟨v42, s30, hinv30, h_v42⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 h_v39 h_v41 dropping hinv29 s29
      store_step with Store.apply_rep s30 v41 v42 _ _ hinv30 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s31, hinv31, h_v43⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 h_v39 dropping h_v41 h_v42 hinv30 s30 v41 v42
      store_step with Store.apply_rep s31 v39 v43 _ _ hinv31 h64 h_v39 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s32, hinv32, h_v44⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v36 dropping h_v39 h_v43 hinv31 s31 v39 v43
      store_step with Store.apply_rep s32 v36 v44 _ _ hinv32 h64 h_v36 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s33, hinv33, h_v45⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 dropping h_v36 h_v44 hinv32 s32 v36 v44
      step as ⟨e_v46, he_v46⟩
      store_step with CtorSpec.eo_bvmul.construct s33 e_v46 (by rw [he_v46]; exact empty_args) hinv33 h64 as ⟨v46, s34, hinv34, h_v46⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 dropping he_v46 hinv33 e_v46 s33
      step as ⟨e_v47, he_v47⟩
      store_step with CtorSpec.eo_concat.construct s34 e_v47 (by rw [he_v47]; exact empty_args) hinv34 h64 as ⟨v47, s35, hinv35, h_v47⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 dropping he_v47 hinv34 e_v47 s34
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s35 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv35 h64 as ⟨v48, s36, hinv36, h_v48⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 h_v47 dropping hinv35 s35
      store_step with Store.apply_rep s36 v47 v48 _ _ hinv36 h64 h_v47 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s37, hinv37, h_v49⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 dropping h_v47 h_v48 hinv36 s36 v47 v48
      step as ⟨e_v50, he_v50⟩
      store_step with CtorSpec.eo_concat.construct s37 e_v50 (by rw [he_v50]; exact empty_args) hinv37 h64 as ⟨v50, s38, hinv38, h_v50⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 h_v49 dropping he_v50 hinv37 e_v50 s37
      store_step with Store.apply_rep s38 v50 v9 _ _ hinv38 h64 h_v50 h_v9 (by ns_tac) (by ns_tac) as ⟨v51, s39, hinv39, h_v51⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 h_v49 dropping h_v50 hinv38 s38 v50
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s39 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv39 h64 as ⟨v52, s40, hinv40, h_v52⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 h_v49 h_v51 dropping hinv39 s39
      store_step with Store.apply_rep s40 v51 v52 _ _ hinv40 h64 h_v51 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s41, hinv41, h_v53⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 h_v49 dropping h_v51 h_v52 hinv40 s40 v51 v52
      store_step with Store.apply_rep s41 v49 v53 _ _ hinv41 h64 h_v49 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s42, hinv42, h_v54⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v46 dropping h_v49 h_v53 hinv41 s41 v49 v53
      store_step with Store.apply_rep s42 v46 v54 _ _ hinv42 h64 h_v46 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s43, hinv43, h_v55⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 dropping h_v46 h_v54 hinv42 s42 v46 v54
      step as ⟨e_v56, he_v56⟩
      store_step with CtorSpec.eo_bvmul.construct s43 e_v56 (by rw [he_v56]; exact empty_args) hinv43 h64 as ⟨v56, s44, hinv44, h_v56⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 dropping he_v56 hinv43 e_v56 s43
      step as ⟨e_v57, he_v57⟩
      store_step with CtorSpec.eo_concat.construct s44 e_v57 (by rw [he_v57]; exact empty_args) hinv44 h64 as ⟨v57, s45, hinv45, h_v57⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 dropping he_v57 hinv44 e_v57 s44
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s45 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv45 h64 as ⟨v58, s46, hinv46, h_v58⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 h_v57 dropping hinv45 s45
      store_step with Store.apply_rep s46 v57 v58 _ _ hinv46 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s47, hinv47, h_v59⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 dropping h_v57 h_v58 hinv46 s46 v57 v58
      step as ⟨e_v60, he_v60⟩
      store_step with CtorSpec.eo_concat.construct s47 e_v60 (by rw [he_v60]; exact empty_args) hinv47 h64 as ⟨v60, s48, hinv48, h_v60⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 h_v59 dropping he_v60 hinv47 e_v60 s47
      store_step with Store.apply_rep s48 v60 v12 _ _ hinv48 h64 h_v60 h_v12 (by ns_tac) (by ns_tac) as ⟨v61, s49, hinv49, h_v61⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 h_v59 dropping h_v60 hinv48 s48 v60
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s49 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv49 h64 as ⟨v62, s50, hinv50, h_v62⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 h_v59 h_v61 dropping hinv49 s49
      store_step with Store.apply_rep s50 v61 v62 _ _ hinv50 h64 h_v61 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s51, hinv51, h_v63⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 h_v59 dropping h_v61 h_v62 hinv50 s50 v61 v62
      store_step with Store.apply_rep s51 v59 v63 _ _ hinv51 h64 h_v59 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s52, hinv52, h_v64⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 dropping h_v59 h_v63 hinv51 s51 v59 v63
      store_step with ih.eo__24eo_5ftypeof s52 v64 _ hinv52 h64 (hG.rem hrem) h_v64 as ⟨v65, s53, hinv53, h_v65⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 h_v56 dropping h_v64 hinv52 s52 v64
      store_step with ih.eo__24eo_5fnil s53 v56 v65 _ _ hinv53 h64 (hG.rem hrem) h_v56 h_v65 as ⟨v66, s54, hinv54, h_v66⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 h_v55 dropping h_v56 h_v65 hinv53 s53 v56 v65
      store_step with Store.apply_mk_rep s54 v55 v66 _ _ hinv54 h64 h_v55 h_v66 as ⟨v67, s55, hinv55, h_v67⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 h_v45 dropping h_v55 h_v66 hinv54 s54 v55 v66
      store_step with Store.apply_mk_rep s55 v45 v67 _ _ hinv55 h64 h_v45 h_v67 as ⟨v68, s56, hinv56, h_v68⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 h_v35 dropping h_v45 h_v67 hinv55 s55 v45 v67
      store_step with Store.apply_mk_rep s56 v35 v68 _ _ hinv56 h64 h_v35 h_v68 as ⟨v69, s57, hinv57, h_v69⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v30 dropping h_v35 h_v68 hinv56 s56 v35 v68
      store_step with Store.apply_mk_rep s57 v30 v69 _ _ hinv57 h64 h_v30 h_v69 as ⟨v70, s58, hinv58, h_v70⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 dropping h_v30 h_v69 hinv57 s57 v30 v69
      step as ⟨e_v71, he_v71⟩
      store_step with CtorSpec.eo_bvor.construct s58 e_v71 (by rw [he_v71]; exact empty_args) hinv58 h64 as ⟨v71, s59, hinv59, h_v71⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 dropping he_v71 hinv58 e_v71 s58
      store_step with ih.eo__24eo_5ftypeof s59 v12 _ hinv59 h64 (hG.rem hrem) h_v12 as ⟨v72, s60, hinv60, h_v72⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 dropping hinv59 s59
      store_step with ih.eo__24bv_5fbitwidth s60 v72 _ hinv60 h64 (hG.rem hrem) h_v72 as ⟨v73, s61, hinv61, h_v73⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 dropping h_v72 hinv60 s60 v72
      store_step with ih.eo__24eo_5ftypeof s61 v12 _ hinv61 h64 (hG.rem hrem) h_v12 as ⟨v74, s62, hinv62, h_v74⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v73 dropping hinv61 s61
      store_step with ih.eo__24bv_5fbitwidth s62 v74 _ hinv62 h64 (hG.rem hrem) h_v74 as ⟨v75, s63, hinv63, h_v75⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v73 dropping h_v74 hinv62 s62 v74
      step as ⟨e_v76, he_v76⟩
      store_step with CtorSpec.eo_extract.construct s63 e_v76 (by rw [he_v76]; rfl) h_v73 h_v75 hinv63 h64 as ⟨v76, s64, hinv64, h_v76⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 dropping h_v73 h_v75 he_v76 hinv63 e_v76 s63 v73 v75
      step as ⟨e_v77, he_v77⟩
      store_step with CtorSpec.eo_bvmul.construct s64 e_v77 (by rw [he_v77]; exact empty_args) hinv64 h64 as ⟨v77, s65, hinv65, h_v77⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 dropping he_v77 hinv64 e_v77 s64
      step as ⟨e_v78, he_v78⟩
      store_step with CtorSpec.eo_concat.construct s65 e_v78 (by rw [he_v78]; exact empty_args) hinv65 h64 as ⟨v78, s66, hinv66, h_v78⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 dropping he_v78 hinv65 e_v78 s65
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s66 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv66 h64 as ⟨v79, s67, hinv67, h_v79⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 h_v78 dropping hinv66 s66
      store_step with Store.apply_rep s67 v78 v79 _ _ hinv67 h64 h_v78 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s68, hinv68, h_v80⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 dropping h_v78 h_v79 hinv67 s67 v78 v79
      step as ⟨e_v81, he_v81⟩
      store_step with CtorSpec.eo_concat.construct s68 e_v81 (by rw [he_v81]; exact empty_args) hinv68 h64 as ⟨v81, s69, hinv69, h_v81⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 h_v80 dropping he_v81 hinv68 e_v81 s68
      store_step with Store.apply_rep s69 v81 v12 _ _ hinv69 h64 h_v81 h_v12 (by ns_tac) (by ns_tac) as ⟨v82, s70, hinv70, h_v82⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 h_v80 dropping h_v81 hinv69 s69 v81
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s70 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv70 h64 as ⟨v83, s71, hinv71, h_v83⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 h_v80 h_v82 dropping hinv70 s70
      store_step with Store.apply_rep s71 v82 v83 _ _ hinv71 h64 h_v82 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s72, hinv72, h_v84⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 h_v80 dropping h_v82 h_v83 hinv71 s71 v82 v83
      store_step with Store.apply_rep s72 v80 v84 _ _ hinv72 h64 h_v80 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s73, hinv73, h_v85⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v77 dropping h_v80 h_v84 hinv72 s72 v80 v84
      store_step with Store.apply_rep s73 v77 v85 _ _ hinv73 h64 h_v77 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s74, hinv74, h_v86⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 dropping h_v77 h_v85 hinv73 s73 v77 v85
      step as ⟨e_v87, he_v87⟩
      store_step with CtorSpec.eo_bvmul.construct s74 e_v87 (by rw [he_v87]; exact empty_args) hinv74 h64 as ⟨v87, s75, hinv75, h_v87⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 dropping he_v87 hinv74 e_v87 s74
      step as ⟨e_v88, he_v88⟩
      store_step with CtorSpec.eo_concat.construct s75 e_v88 (by rw [he_v88]; exact empty_args) hinv75 h64 as ⟨v88, s76, hinv76, h_v88⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 dropping he_v88 hinv75 e_v88 s75
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s76 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv76 h64 as ⟨v89, s77, hinv77, h_v89⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 h_v88 dropping hinv76 s76
      store_step with Store.apply_rep s77 v88 v89 _ _ hinv77 h64 h_v88 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s78, hinv78, h_v90⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 dropping h_v88 h_v89 hinv77 s77 v88 v89
      step as ⟨e_v91, he_v91⟩
      store_step with CtorSpec.eo_concat.construct s78 e_v91 (by rw [he_v91]; exact empty_args) hinv78 h64 as ⟨v91, s79, hinv79, h_v91⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 h_v90 dropping he_v91 hinv78 e_v91 s78
      store_step with Store.apply_rep s79 v91 v9 _ _ hinv79 h64 h_v91 h_v9 (by ns_tac) (by ns_tac) as ⟨v92, s80, hinv80, h_v92⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 h_v90 dropping h_v91 hinv79 s79 v91
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s80 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv80 h64 as ⟨v93, s81, hinv81, h_v93⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 h_v90 h_v92 dropping hinv80 s80
      store_step with Store.apply_rep s81 v92 v93 _ _ hinv81 h64 h_v92 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s82, hinv82, h_v94⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 h_v90 dropping h_v92 h_v93 hinv81 s81 v92 v93
      store_step with Store.apply_rep s82 v90 v94 _ _ hinv82 h64 h_v90 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s83, hinv83, h_v95⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v87 dropping h_v90 h_v94 hinv82 s82 v90 v94
      store_step with Store.apply_rep s83 v87 v95 _ _ hinv83 h64 h_v87 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s84, hinv84, h_v96⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 dropping h_v87 h_v95 hinv83 s83 v87 v95
      step as ⟨e_v97, he_v97⟩
      store_step with CtorSpec.eo_bvmul.construct s84 e_v97 (by rw [he_v97]; exact empty_args) hinv84 h64 as ⟨v97, s85, hinv85, h_v97⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 dropping he_v97 hinv84 e_v97 s84
      step as ⟨e_v98, he_v98⟩
      store_step with CtorSpec.eo_concat.construct s85 e_v98 (by rw [he_v98]; exact empty_args) hinv85 h64 as ⟨v98, s86, hinv86, h_v98⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 dropping he_v98 hinv85 e_v98 s85
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s86 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv86 h64 as ⟨v99, s87, hinv87, h_v99⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 h_v98 dropping hinv86 s86
      store_step with Store.apply_rep s87 v98 v99 _ _ hinv87 h64 h_v98 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s88, hinv88, h_v100⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 dropping h_v98 h_v99 hinv87 s87 v98 v99
      step as ⟨e_v101, he_v101⟩
      store_step with CtorSpec.eo_concat.construct s88 e_v101 (by rw [he_v101]; exact empty_args) hinv88 h64 as ⟨v101, s89, hinv89, h_v101⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 h_v100 dropping he_v101 hinv88 e_v101 s88
      store_step with Store.apply_rep s89 v101 v12 _ _ hinv89 h64 h_v101 h_v12 (by ns_tac) (by ns_tac) as ⟨v102, s90, hinv90, h_v102⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 h_v100 dropping h_v101 hinv89 s89 v101
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s90 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv90 h64 as ⟨v103, s91, hinv91, h_v103⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 h_v100 h_v102 dropping hinv90 s90
      store_step with Store.apply_rep s91 v102 v103 _ _ hinv91 h64 h_v102 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s92, hinv92, h_v104⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 h_v100 dropping h_v102 h_v103 hinv91 s91 v102 v103
      store_step with Store.apply_rep s92 v100 v104 _ _ hinv92 h64 h_v100 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s93, hinv93, h_v105⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 dropping h_v100 h_v104 hinv92 s92 v100 v104
      store_step with ih.eo__24eo_5ftypeof s93 v105 _ hinv93 h64 (hG.rem hrem) h_v105 as ⟨v106, s94, hinv94, h_v106⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 h_v97 dropping h_v105 hinv93 s93 v105
      store_step with ih.eo__24eo_5fnil s94 v97 v106 _ _ hinv94 h64 (hG.rem hrem) h_v97 h_v106 as ⟨v107, s95, hinv95, h_v107⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 h_v96 dropping h_v106 h_v97 hinv94 s94 v106 v97
      store_step with Store.apply_mk_rep s95 v96 v107 _ _ hinv95 h64 h_v96 h_v107 as ⟨v108, s96, hinv96, h_v108⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 h_v86 dropping h_v107 h_v96 hinv95 s95 v107 v96
      store_step with Store.apply_mk_rep s96 v86 v108 _ _ hinv96 h64 h_v86 h_v108 as ⟨v109, s97, hinv97, h_v109⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 h_v76 dropping h_v108 h_v86 hinv96 s96 v108 v86
      store_step with Store.apply_mk_rep s97 v76 v109 _ _ hinv97 h64 h_v76 h_v109 as ⟨v110, s98, hinv98, h_v110⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 dropping h_v109 h_v76 hinv97 s97 v109 v76
      store_step with ih.eo__24eo_5ftypeof s98 v110 _ hinv98 h64 (hG.rem hrem) h_v110 as ⟨v111, s99, hinv99, h_v111⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 h_v71 dropping h_v110 hinv98 s98 v110
      store_step with ih.eo__24eo_5fnil s99 v71 v111 _ _ hinv99 h64 (hG.rem hrem) h_v71 h_v111 as ⟨v112, s100, hinv100, h_v112⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v70 dropping h_v111 h_v71 hinv99 s99 v111 v71
      store_step with Store.apply_mk_rep s100 v70 v112 _ _ hinv100 h64 h_v70 h_v112 as ⟨v113, s101, hinv101, h_v113⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 dropping h_v112 h_v70 hinv100 s100 v112 v70
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s101 1#u32 (1) (by scalar_tac) hinv101 h64 as ⟨v114, s102, hinv102, h_v114⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping hinv101 s101
      store_step with ih.eo__24eo_5ftypeof s102 v12 _ hinv102 h64 (hG.rem hrem) h_v12 as ⟨v115, s103, hinv103, h_v115⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v114 dropping hinv102 s102
      store_step with ih.eo__24bv_5fbitwidth s103 v115 _ hinv103 h64 (hG.rem hrem) h_v115 as ⟨v116, s104, hinv104, h_v116⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v114 dropping h_v115 hinv103 s103 v115
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s104 1#u32 (-1) (by scalar_tac) hinv104 h64 as ⟨v117, s105, hinv105, h_v117⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v114 h_v116 dropping hinv104 s104
      step as ⟨e_v118, he_v118⟩
      store_step with Store.builtin_spec_add s105 e_v118 (by rw [he_v118]; rfl) h_v116 h_v117 hinv105 h64 as ⟨v118, s106, hinv106, h_v118⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v114 dropping h_v116 h_v117 he_v118 hinv105 e_v118 s105 v116 v117
      step as ⟨e_v119, he_v119⟩
      store_step with Store.builtin_spec_add s106 e_v119 (by rw [he_v119]; rfl) h_v114 h_v118 hinv106 h64 as ⟨v119, s107, hinv107, h_v119⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_v114 h_v118 he_v119 hinv106 e_v119 s106 v114 v118
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s107 1#u32 (-1) (by scalar_tac) hinv107 h64 as ⟨v120, s108, hinv108, h_v120⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v119 dropping hinv107 s107
      step as ⟨e_v121, he_v121⟩
      store_step with Store.builtin_spec_add s108 e_v121 (by rw [he_v121]; rfl) h_v119 h_v120 hinv108 h64 as ⟨v121, s109, hinv109, h_v121⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_v119 h_v120 he_v121 hinv108 e_v121 s108 v119 v120
      step as ⟨e_v122, he_v122⟩
      store_step with Store.builtin_spec_is_neg s109 e_v122 (by rw [he_v122]; rfl) h_v121 hinv109 h64 as ⟨v122, s110, hinv110, h_v122⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_v121 he_v122 hinv109 e_v122 s109 v121
      store_step with Store.literal_boolean_spec s110 false hinv110 h64 as ⟨v123, s111, hinv111, h_v123⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v122 dropping hinv110 s110
      have h_req_v137 := (show requires_1_eo__24eo_5fprog_5fbv_2dumulo_2delim s111 v122 v123 v12 ⦃ r s' => s'.Inv ∧ s111.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold requires_1_eo__24eo_5fprog_5fbv_2dumulo_2delim
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s111
        req_same v122 v123 with h_v122 h_v123 using hinv111 hG
        req_stuck h_v122 as hq_v122 using hinv111 hG
        step as ⟨e_v124, he_v124⟩
        store_step with CtorSpec.eo__40_40TypedList_2econs.construct s111 e_v124 (by rw [he_v124]; exact empty_args) hinv111 h64 as ⟨v124, s112, hinv112, h_v124⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_v122 h_v123 he_v124 hinv111 e_v124 s111 v122 v123
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s112 0#u32 (0) (by scalar_tac) hinv112 h64 as ⟨v125, s113, hinv113, h_v125⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 dropping hinv112 s112
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s113 1#u32 (1) (by scalar_tac) hinv113 h64 as ⟨v126, s114, hinv114, h_v126⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 dropping hinv113 s113
        store_step with ih.eo__24eo_5ftypeof s114 v12 _ hinv114 h64 (hG.rem hrem) h_v12 as ⟨v127, s115, hinv115, h_v127⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 h_v126 dropping hinv114 s114
        store_step with ih.eo__24bv_5fbitwidth s115 v127 _ hinv115 h64 (hG.rem hrem) h_v127 as ⟨v128, s116, hinv116, h_v128⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 h_v126 dropping h_v127 hinv115 s115 v127
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_neg_u32_spec s116 1#u32 (-1) (by scalar_tac) hinv116 h64 as ⟨v129, s117, hinv117, h_v129⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 h_v126 h_v128 dropping hinv116 s116
        step as ⟨e_v130, he_v130⟩
        store_step with Store.builtin_spec_add s117 e_v130 (by rw [he_v130]; rfl) h_v128 h_v129 hinv117 h64 as ⟨v130, s118, hinv118, h_v130⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 h_v126 dropping h_v128 h_v129 he_v130 hinv117 e_v130 s117 v128 v129
        step as ⟨e_v131, he_v131⟩
        store_step with Store.builtin_spec_add s118 e_v131 (by rw [he_v131]; rfl) h_v126 h_v130 hinv118 h64 as ⟨v131, s119, hinv119, h_v131⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 dropping h_v126 h_v130 he_v131 hinv118 e_v131 s118 v126 v130
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_neg_u32_spec s119 1#u32 (-1) (by scalar_tac) hinv119 h64 as ⟨v132, s120, hinv120, h_v132⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 h_v131 dropping hinv119 s119
        step as ⟨e_v133, he_v133⟩
        store_step with Store.builtin_spec_add s120 e_v133 (by rw [he_v133]; rfl) h_v131 h_v132 hinv120 h64 as ⟨v133, s121, hinv121, h_v133⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v124 h_v125 dropping h_v131 h_v132 he_v133 hinv120 e_v133 s120 v131 v132
        step as ⟨e_v134, he_v134⟩
        store_step with Store.builtin_spec_list_repeat n ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s121 e_v134 (by rw [he_v134]; rfl) h_v124 h_v125 h_v133 hinv121 h64 (hG.rem hrem) op_not_left_eo__40_40TypedList_2econs as ⟨v134, s122, hinv122, h_v134⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_v124 h_v125 h_v133 he_v134 hinv121 e_v134 s121 v124 v125 v133
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s122 1#u32 (1) (by scalar_tac) hinv122 h64 as ⟨v135, s123, hinv123, h_v135⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v134 dropping hinv122 s122
        store_step with ih.eo__24iota_5frec s123 v134 v135 _ _ hinv123 h64 (hG.rem hrem) h_v134 h_v135 as ⟨v136, s124, hinv124, h_v136⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_v134 h_v135 hinv123 s123 v134 v135
        req_done hinv124 hG with h_v136 using hq_v122)
      store_step with h_req_v137 as ⟨v137, s125, hinv125, h_v137⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 dropping h_req_v137 h_v122 h_v123 hinv111 s111 v122 v123
      store_step with ih.eo__24eo_5ftypeof s125 v12 _ hinv125 h64 (hG.rem hrem) h_v12 as ⟨v138, s126, hinv126, h_v138⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v137 dropping hinv125 s125
      store_step with ih.eo__24bv_5fbitwidth s126 v138 _ hinv126 h64 (hG.rem hrem) h_v138 as ⟨v139, s127, hinv127, h_v139⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 h_v29 h_v113 h_v137 dropping h_v138 hinv126 s126 v138
      store_step with ih.eo__24bv_5fumulo_5felim_5frec s127 v12 v9 v29 v113 v137 v139 _ _ _ _ _ _ hinv127 h64 (hG.rem hrem) h_v12 h_v9 h_v29 h_v113 h_v137 h_v139 as ⟨v140, s128, hinv128, h_v140⟩ growing hG carrying h_v2 h_v9 h_v12 h_v19 dropping h_v113 h_v137 h_v139 h_v29 hinv127 s127 v113 v137 v139 v29
      store_step with Store.apply_mk_rep s128 v19 v140 _ _ hinv128 h64 h_v19 h_v140 as ⟨v141, s129, hinv129, h_v141⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v140 h_v19 hinv128 s128 v140 v19
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s129 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv129 h64 as ⟨v142, s130, hinv130, h_v142⟩ growing hG carrying h_v2 h_v9 h_v12 h_v141 dropping hinv129 s129
      store_step with Store.apply_mk_rep s130 v141 v142 _ _ hinv130 h64 h_v141 h_v142 as ⟨v143, s131, hinv131, h_v143⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v141 h_v142 hinv130 s130 v141 v142
      ite_done hinv131 hG with (eo_ite_false_rep _ hx_18 h_v143)
    · ite_branch hbv_18
      ite_stuck hinv6 hG with hx_18)
  store_step with h_ite_v144 as ⟨v144, s7, hinv7, h_v144⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_ite_v144 h_v17 hinv6 s6 v17
  have h_req_v151 := (show requires_12_eo__24eo_5fprog_5fbv_2dumulo_2delim s7 v144 v2 v12 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_12_eo__24eo_5fprog_5fbv_2dumulo_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v144 v2 with h_v144 h_v2 using hinv7 hG
    req_stuck h_v144 as hq_v144 using hinv7 hG
    step as ⟨e_v145, he_v145⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v145 (by rw [he_v145]; exact empty_args) hinv7 h64 as ⟨v145, s8, hinv8, h_v145⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v144 he_v145 hinv7 e_v145 s7 v144
    step as ⟨e_v146, he_v146⟩
    store_step with CtorSpec.eo_bvumulo.construct s8 e_v146 (by rw [he_v146]; exact empty_args) hinv8 h64 as ⟨v146, s9, hinv9, h_v146⟩ growing hG carrying h_v2 h_v9 h_v12 h_v145 dropping he_v146 hinv8 e_v146 s8
    store_step with Store.apply_rep s9 v146 v12 _ _ hinv9 h64 h_v146 h_v12 (by ns_tac) (by ns_tac) as ⟨v147, s10, hinv10, h_v147⟩ growing hG carrying h_v2 h_v9 h_v145 dropping h_v12 h_v146 hinv9 s9 v12 v146
    store_step with Store.apply_rep s10 v147 v9 _ _ hinv10 h64 h_v147 h_v9 (by ns_tac) (by ns_tac) as ⟨v148, s11, hinv11, h_v148⟩ growing hG carrying h_v2 h_v145 dropping h_v147 h_v9 hinv10 s10 v147 v9
    store_step with Store.apply_rep s11 v145 v148 _ _ hinv11 h64 h_v145 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s12, hinv12, h_v149⟩ growing hG carrying h_v2 dropping h_v145 h_v148 hinv11 s11 v145 v148
    store_step with Store.apply_rep s12 v149 v2 _ _ hinv12 h64 h_v149 h_v2 (by ns_tac) (by ns_tac) as ⟨v150, s13, hinv13, h_v150⟩ growing hG carrying dropping h_v149 h_v2 hinv12 s12 v149 v2
    req_done hinv13 hG with h_v150 using hq_v144)
  store_step with h_req_v151 as ⟨v151, s14, hinv14, h_v151⟩ growing hG carrying dropping h_req_v151 h_v12 h_v144 h_v2 h_v9 hinv7 s7 v12 v144 v2 v9
  case_done hinv14 hG with h_v151 in EoCases.__eo_prog_bv_umulo_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

set_option maxHeartbeats 5000000 in
/-- logos's `__eo_prog_bv_umulo_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dumulo_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_umulo_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_umulo_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_umulo_elim
  unfold EoCases.__eo_prog_bv_umulo_elim.case_0
  logos_eq

set_option maxHeartbeats 5000000 in
theorem body_eo__24eo_5fprog_5fbv_2dumulo_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dumulo_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_umulo_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dumulo_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dumulo_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dumulo_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_umulo_elim.case_0

set_option maxHeartbeats 5000000 in
theorem eo__24eo_5fprog_5fbv_2dumulo_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dumulo_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dumulo_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dumulo_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_umulo_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dumulo_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
