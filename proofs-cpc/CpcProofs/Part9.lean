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

set_option maxHeartbeats 19770000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_smulo_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_smulo_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_smulo_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_smulo_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_smulo_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_smulo_elim.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_smulo_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_bvsmulo.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_v2 h_v9 h_v11 h_v12 dropping h_v4 h_v5 h_v6 h_v8 he_v13 hinv1 e_v13 s1 v4 v5 v6 v8
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_smulo_elim.case_0
  store_step with ih.eo__24eo_5ftypeof s2 v12 _ hinv2 h64 (hG.rem hrem) h_v12 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v11 h_v13 hinv2 s2 v11 v13
  store_step with ih.eo__24bv_5fbitwidth s3 v14 _ hinv3 h64 (hG.rem hrem) h_v14 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v14 hinv3 s3 v14
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_v2 h_v9 h_v12 h_v15 dropping hinv4 s4
  step as ⟨e_v17, he_v17⟩
  store_step with Store.builtin_spec_eq s5 e_v17 (by rw [he_v17]; rfl) h_v15 h_v16 hinv5 h64 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v15 h_v16 he_v17 hinv5 e_v17 s5 v15 v16
  have h_ite_v663 := (show if_55_eo__24eo_5fprog_5fbv_2dsmulo_2delim s6 v17 v12 v9 ⦃ r s' => s'.Inv ∧ s6.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_55_eo__24eo_5fprog_5fbv_2dsmulo_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s6
    rcases Store.boolean_value_term h_v17 with ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩ | ⟨hx_18, hbv_18⟩
    · ite_branch hbv_18
      step as ⟨e_v18, he_v18⟩
      store_step with CtorSpec.eo__3d.construct s6 e_v18 (by rw [he_v18]; exact empty_args) hinv6 h64 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v17 he_v18 e_v18 v17
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo_bvand.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 dropping he_v19 e_v19
      store_step with Store.apply_rep s8 v19 v12 _ _ hinv8 h64 h_v19 h_v12 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 dropping h_v19 v19
      step as ⟨e_v21, he_v21⟩
      store_step with CtorSpec.eo_bvand.construct s9 e_v21 (by rw [he_v21]; exact empty_args) hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 h_v20 dropping he_v21 e_v21
      store_step with Store.apply_rep s10 v21 v9 _ _ hinv10 h64 h_v21 h_v9 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 h_v20 dropping h_v21 v21
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo_bvand.construct s11 e_v23 (by rw [he_v23]; exact empty_args) hinv11 h64 as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 h_v20 h_v22 dropping he_v23 e_v23
      store_step with ih.eo__24eo_5ftypeof s12 v12 _ hinv12 h64 (hG.rem hrem) h_v12 as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 h_v20 h_v22 h_v23 dropping
      store_step with ih.eo__24eo_5fnil s13 v23 v24 _ _ hinv13 h64 (hG.rem hrem) h_v23 h_v24 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 h_v20 h_v22 dropping h_v23 h_v24 v23 v24
      store_step with Store.apply_mk_rep s14 v22 v25 _ _ hinv14 h64 h_v22 h_v25 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 h_v20 dropping h_v22 h_v25 v22 v25
      store_step with Store.apply_mk_rep s15 v20 v26 _ _ hinv15 h64 h_v20 h_v26 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_v2 h_v9 h_v12 h_v18 dropping h_v20 h_v26 v20 v26
      store_step with Store.apply_mk_rep s16 v18 v27 _ _ hinv16 h64 h_v18 h_v27 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v18 h_v27 v18 v27
      try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
      store_step with Store.literal_binary_u32_spec s17 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv17 h64 as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_v2 h_v9 h_v12 h_v28 dropping
      store_step with Store.apply_mk_rep s18 v28 v29 _ _ hinv18 h64 h_v28 h_v29 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v28 h_v29 v28 v29
      ite_done hinv19 hG with (eo_ite_true_rep _ hx_18 h_v30)
    · ite_branch hbv_18
      store_step with ih.eo__24eo_5ftypeof s6 v12 _ hinv6 h64 (hG.rem hrem) h_v12 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v17 v17
      store_step with ih.eo__24bv_5fbitwidth s7 v31 _ hinv7 h64 (hG.rem hrem) h_v31 as ⟨v32, s8, hinv8, h_v32⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v31 v31
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s8 2#u32 (2) (by scalar_tac) hinv8 h64 as ⟨v33, s9, hinv9, h_v33⟩ growing hG carrying h_v2 h_v9 h_v12 h_v32 dropping
      step as ⟨e_v34, he_v34⟩
      store_step with Store.builtin_spec_eq s9 e_v34 (by rw [he_v34]; rfl) h_v32 h_v33 hinv9 h64 as ⟨v34, s10, hinv10, h_v34⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v32 h_v33 he_v34 e_v34 v32 v33
      have h_ite_v662 := (show if_53_eo__24eo_5fprog_5fbv_2dsmulo_2delim s10 v34 v12 v9 ⦃ r s' => s'.Inv ∧ s10.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_53_eo__24eo_5fprog_5fbv_2dsmulo_2delim
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s10
        rcases Store.boolean_value_term h_v34 with ⟨hx_35, hbv_35⟩ | ⟨hx_35, hbv_35⟩ | ⟨hx_35, hbv_35⟩
        · ite_branch hbv_35
          step as ⟨e_v35, he_v35⟩
          store_step with CtorSpec.eo__3d.construct s10 e_v35 (by rw [he_v35]; exact empty_args) hinv10 h64 as ⟨v35, s11, hinv11, h_v35⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v34 he_v35 e_v35 v34
          step as ⟨e_v36, he_v36⟩
          store_step with CtorSpec.eo_bvxor.construct s11 e_v36 (by rw [he_v36]; exact empty_args) hinv11 h64 as ⟨v36, s12, hinv12, h_v36⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 dropping he_v36 e_v36
          store_step with ih.eo__24eo_5ftypeof s12 v12 _ hinv12 h64 (hG.rem hrem) h_v12 as ⟨v37, s13, hinv13, h_v37⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 dropping
          store_step with ih.eo__24bv_5fbitwidth s13 v37 _ hinv13 h64 (hG.rem hrem) h_v37 as ⟨v38, s14, hinv14, h_v38⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 dropping h_v37 v37
          store_step with ih.eo__24eo_5ftypeof s14 v12 _ hinv14 h64 (hG.rem hrem) h_v12 as ⟨v39, s15, hinv15, h_v39⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v38 dropping
          store_step with ih.eo__24bv_5fbitwidth s15 v39 _ hinv15 h64 (hG.rem hrem) h_v39 as ⟨v40, s16, hinv16, h_v40⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v38 dropping h_v39 v39
          step as ⟨e_v41, he_v41⟩
          store_step with CtorSpec.eo_extract.construct s16 e_v41 (by rw [he_v41]; rfl) h_v38 h_v40 hinv16 h64 as ⟨v41, s17, hinv17, h_v41⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 dropping h_v38 h_v40 he_v41 e_v41 v38 v40
          step as ⟨e_v42, he_v42⟩
          store_step with CtorSpec.eo_bvmul.construct s17 e_v42 (by rw [he_v42]; exact empty_args) hinv17 h64 as ⟨v42, s18, hinv18, h_v42⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 dropping he_v42 e_v42
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s18 1#u32 (1) (by scalar_tac) hinv18 h64 as ⟨v43, s19, hinv19, h_v43⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v42 dropping
          step as ⟨e_v44, he_v44⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s19 e_v44 (by rw [he_v44]; rfl) h_v43 hinv19 h64 as ⟨v44, s20, hinv20, h_v44⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v42 dropping h_v43 he_v44 e_v44 v43
          store_step with Store.apply_rep s20 v44 v12 _ _ hinv20 h64 h_v44 h_v12 (by ns_tac) (by ns_tac) as ⟨v45, s21, hinv21, h_v45⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v42 dropping h_v44 v44
          store_step with Store.apply_rep s21 v42 v45 _ _ hinv21 h64 h_v42 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s22, hinv22, h_v46⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 dropping h_v42 h_v45 v42 v45
          step as ⟨e_v47, he_v47⟩
          store_step with CtorSpec.eo_bvmul.construct s22 e_v47 (by rw [he_v47]; exact empty_args) hinv22 h64 as ⟨v47, s23, hinv23, h_v47⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 dropping he_v47 e_v47
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s23 1#u32 (1) (by scalar_tac) hinv23 h64 as ⟨v48, s24, hinv24, h_v48⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v47 dropping
          step as ⟨e_v49, he_v49⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s24 e_v49 (by rw [he_v49]; rfl) h_v48 hinv24 h64 as ⟨v49, s25, hinv25, h_v49⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v47 dropping h_v48 he_v49 e_v49 v48
          store_step with Store.apply_rep s25 v49 v9 _ _ hinv25 h64 h_v49 h_v9 (by ns_tac) (by ns_tac) as ⟨v50, s26, hinv26, h_v50⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v47 dropping h_v49 v49
          store_step with Store.apply_rep s26 v47 v50 _ _ hinv26 h64 h_v47 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s27, hinv27, h_v51⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 dropping h_v47 h_v50 v47 v50
          step as ⟨e_v52, he_v52⟩
          store_step with CtorSpec.eo_bvmul.construct s27 e_v52 (by rw [he_v52]; exact empty_args) hinv27 h64 as ⟨v52, s28, hinv28, h_v52⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v51 dropping he_v52 e_v52
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s28 1#u32 (1) (by scalar_tac) hinv28 h64 as ⟨v53, s29, hinv29, h_v53⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v51 h_v52 dropping
          step as ⟨e_v54, he_v54⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s29 e_v54 (by rw [he_v54]; rfl) h_v53 hinv29 h64 as ⟨v54, s30, hinv30, h_v54⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v51 h_v52 dropping h_v53 he_v54 e_v54 v53
          store_step with Store.apply_rep s30 v54 v12 _ _ hinv30 h64 h_v54 h_v12 (by ns_tac) (by ns_tac) as ⟨v55, s31, hinv31, h_v55⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v51 h_v52 dropping h_v54 v54
          store_step with ih.eo__24eo_5ftypeof s31 v55 _ hinv31 h64 (hG.rem hrem) h_v55 as ⟨v56, s32, hinv32, h_v56⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v51 h_v52 dropping h_v55 v55
          store_step with ih.eo__24eo_5fnil s32 v52 v56 _ _ hinv32 h64 (hG.rem hrem) h_v52 h_v56 as ⟨v57, s33, hinv33, h_v57⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 h_v51 dropping h_v52 h_v56 v52 v56
          store_step with Store.apply_mk_rep s33 v51 v57 _ _ hinv33 h64 h_v51 h_v57 as ⟨v58, s34, hinv34, h_v58⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 h_v46 dropping h_v51 h_v57 v51 v57
          store_step with Store.apply_mk_rep s34 v46 v58 _ _ hinv34 h64 h_v46 h_v58 as ⟨v59, s35, hinv35, h_v59⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 h_v41 dropping h_v46 h_v58 v46 v58
          store_step with Store.apply_mk_rep s35 v41 v59 _ _ hinv35 h64 h_v41 h_v59 as ⟨v60, s36, hinv36, h_v60⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v36 dropping h_v41 h_v59 v41 v59
          store_step with Store.apply_mk_rep s36 v36 v60 _ _ hinv36 h64 h_v36 h_v60 as ⟨v61, s37, hinv37, h_v61⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 dropping h_v36 h_v60 v36 v60
          step as ⟨e_v62, he_v62⟩
          store_step with CtorSpec.eo_bvxor.construct s37 e_v62 (by rw [he_v62]; exact empty_args) hinv37 h64 as ⟨v62, s38, hinv38, h_v62⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 dropping he_v62 e_v62
          store_step with ih.eo__24eo_5ftypeof s38 v12 _ hinv38 h64 (hG.rem hrem) h_v12 as ⟨v63, s39, hinv39, h_v63⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 dropping
          store_step with ih.eo__24bv_5fbitwidth s39 v63 _ hinv39 h64 (hG.rem hrem) h_v63 as ⟨v64, s40, hinv40, h_v64⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 dropping h_v63 v63
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s40 1#u32 (-1) (by scalar_tac) hinv40 h64 as ⟨v65, s41, hinv41, h_v65⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v64 dropping
          step as ⟨e_v66, he_v66⟩
          store_step with Store.builtin_spec_add s41 e_v66 (by rw [he_v66]; rfl) h_v64 h_v65 hinv41 h64 as ⟨v66, s42, hinv42, h_v66⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 dropping h_v64 h_v65 he_v66 e_v66 v64 v65
          store_step with ih.eo__24eo_5ftypeof s42 v12 _ hinv42 h64 (hG.rem hrem) h_v12 as ⟨v67, s43, hinv43, h_v67⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v66 dropping
          store_step with ih.eo__24bv_5fbitwidth s43 v67 _ hinv43 h64 (hG.rem hrem) h_v67 as ⟨v68, s44, hinv44, h_v68⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v66 dropping h_v67 v67
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s44 1#u32 (-1) (by scalar_tac) hinv44 h64 as ⟨v69, s45, hinv45, h_v69⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v66 h_v68 dropping
          step as ⟨e_v70, he_v70⟩
          store_step with Store.builtin_spec_add s45 e_v70 (by rw [he_v70]; rfl) h_v68 h_v69 hinv45 h64 as ⟨v70, s46, hinv46, h_v70⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v66 dropping h_v68 h_v69 he_v70 e_v70 v68 v69
          step as ⟨e_v71, he_v71⟩
          store_step with CtorSpec.eo_extract.construct s46 e_v71 (by rw [he_v71]; rfl) h_v66 h_v70 hinv46 h64 as ⟨v71, s47, hinv47, h_v71⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 dropping h_v66 h_v70 he_v71 e_v71 v66 v70
          step as ⟨e_v72, he_v72⟩
          store_step with CtorSpec.eo_bvmul.construct s47 e_v72 (by rw [he_v72]; exact empty_args) hinv47 h64 as ⟨v72, s48, hinv48, h_v72⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 dropping he_v72 e_v72
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s48 1#u32 (1) (by scalar_tac) hinv48 h64 as ⟨v73, s49, hinv49, h_v73⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v72 dropping
          step as ⟨e_v74, he_v74⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s49 e_v74 (by rw [he_v74]; rfl) h_v73 hinv49 h64 as ⟨v74, s50, hinv50, h_v74⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v72 dropping h_v73 he_v74 e_v74 v73
          store_step with Store.apply_rep s50 v74 v12 _ _ hinv50 h64 h_v74 h_v12 (by ns_tac) (by ns_tac) as ⟨v75, s51, hinv51, h_v75⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v72 dropping h_v74 v74
          store_step with Store.apply_rep s51 v72 v75 _ _ hinv51 h64 h_v72 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s52, hinv52, h_v76⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 dropping h_v72 h_v75 v72 v75
          step as ⟨e_v77, he_v77⟩
          store_step with CtorSpec.eo_bvmul.construct s52 e_v77 (by rw [he_v77]; exact empty_args) hinv52 h64 as ⟨v77, s53, hinv53, h_v77⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 dropping he_v77 e_v77
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s53 1#u32 (1) (by scalar_tac) hinv53 h64 as ⟨v78, s54, hinv54, h_v78⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v77 dropping
          step as ⟨e_v79, he_v79⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s54 e_v79 (by rw [he_v79]; rfl) h_v78 hinv54 h64 as ⟨v79, s55, hinv55, h_v79⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v77 dropping h_v78 he_v79 e_v79 v78
          store_step with Store.apply_rep s55 v79 v9 _ _ hinv55 h64 h_v79 h_v9 (by ns_tac) (by ns_tac) as ⟨v80, s56, hinv56, h_v80⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v77 dropping h_v79 v79
          store_step with Store.apply_rep s56 v77 v80 _ _ hinv56 h64 h_v77 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s57, hinv57, h_v81⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 dropping h_v77 h_v80 v77 v80
          step as ⟨e_v82, he_v82⟩
          store_step with CtorSpec.eo_bvmul.construct s57 e_v82 (by rw [he_v82]; exact empty_args) hinv57 h64 as ⟨v82, s58, hinv58, h_v82⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v81 dropping he_v82 e_v82
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s58 1#u32 (1) (by scalar_tac) hinv58 h64 as ⟨v83, s59, hinv59, h_v83⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v81 h_v82 dropping
          step as ⟨e_v84, he_v84⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s59 e_v84 (by rw [he_v84]; rfl) h_v83 hinv59 h64 as ⟨v84, s60, hinv60, h_v84⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v81 h_v82 dropping h_v83 he_v84 e_v84 v83
          store_step with Store.apply_rep s60 v84 v12 _ _ hinv60 h64 h_v84 h_v12 (by ns_tac) (by ns_tac) as ⟨v85, s61, hinv61, h_v85⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v81 h_v82 dropping h_v84 v84
          store_step with ih.eo__24eo_5ftypeof s61 v85 _ hinv61 h64 (hG.rem hrem) h_v85 as ⟨v86, s62, hinv62, h_v86⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v81 h_v82 dropping h_v85 v85
          store_step with ih.eo__24eo_5fnil s62 v82 v86 _ _ hinv62 h64 (hG.rem hrem) h_v82 h_v86 as ⟨v87, s63, hinv63, h_v87⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 h_v81 dropping h_v82 h_v86 v82 v86
          store_step with Store.apply_mk_rep s63 v81 v87 _ _ hinv63 h64 h_v81 h_v87 as ⟨v88, s64, hinv64, h_v88⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 h_v76 dropping h_v81 h_v87 v81 v87
          store_step with Store.apply_mk_rep s64 v76 v88 _ _ hinv64 h64 h_v76 h_v88 as ⟨v89, s65, hinv65, h_v89⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 h_v71 dropping h_v76 h_v88 v76 v88
          store_step with Store.apply_mk_rep s65 v71 v89 _ _ hinv65 h64 h_v71 h_v89 as ⟨v90, s66, hinv66, h_v90⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v62 dropping h_v71 h_v89 v71 v89
          store_step with Store.apply_mk_rep s66 v62 v90 _ _ hinv66 h64 h_v62 h_v90 as ⟨v91, s67, hinv67, h_v91⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 dropping h_v62 h_v90 v62 v90
          step as ⟨e_v92, he_v92⟩
          store_step with CtorSpec.eo_bvxor.construct s67 e_v92 (by rw [he_v92]; exact empty_args) hinv67 h64 as ⟨v92, s68, hinv68, h_v92⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 dropping he_v92 e_v92
          store_step with ih.eo__24eo_5ftypeof s68 v12 _ hinv68 h64 (hG.rem hrem) h_v12 as ⟨v93, s69, hinv69, h_v93⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 dropping
          store_step with ih.eo__24bv_5fbitwidth s69 v93 _ hinv69 h64 (hG.rem hrem) h_v93 as ⟨v94, s70, hinv70, h_v94⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 dropping h_v93 v93
          store_step with ih.eo__24eo_5ftypeof s70 v12 _ hinv70 h64 (hG.rem hrem) h_v12 as ⟨v95, s71, hinv71, h_v95⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v94 dropping
          store_step with ih.eo__24bv_5fbitwidth s71 v95 _ hinv71 h64 (hG.rem hrem) h_v95 as ⟨v96, s72, hinv72, h_v96⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v94 dropping h_v95 v95
          step as ⟨e_v97, he_v97⟩
          store_step with CtorSpec.eo_extract.construct s72 e_v97 (by rw [he_v97]; rfl) h_v94 h_v96 hinv72 h64 as ⟨v97, s73, hinv73, h_v97⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 dropping h_v94 h_v96 he_v97 e_v97 v94 v96
          step as ⟨e_v98, he_v98⟩
          store_step with CtorSpec.eo_bvmul.construct s73 e_v98 (by rw [he_v98]; exact empty_args) hinv73 h64 as ⟨v98, s74, hinv74, h_v98⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 dropping he_v98 e_v98
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s74 1#u32 (1) (by scalar_tac) hinv74 h64 as ⟨v99, s75, hinv75, h_v99⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v98 dropping
          step as ⟨e_v100, he_v100⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s75 e_v100 (by rw [he_v100]; rfl) h_v99 hinv75 h64 as ⟨v100, s76, hinv76, h_v100⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v98 dropping h_v99 he_v100 e_v100 v99
          store_step with Store.apply_rep s76 v100 v12 _ _ hinv76 h64 h_v100 h_v12 (by ns_tac) (by ns_tac) as ⟨v101, s77, hinv77, h_v101⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v98 dropping h_v100 v100
          store_step with Store.apply_rep s77 v98 v101 _ _ hinv77 h64 h_v98 h_v101 (by ns_tac) (by ns_tac) as ⟨v102, s78, hinv78, h_v102⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 dropping h_v101 h_v98 v101 v98
          step as ⟨e_v103, he_v103⟩
          store_step with CtorSpec.eo_bvmul.construct s78 e_v103 (by rw [he_v103]; exact empty_args) hinv78 h64 as ⟨v103, s79, hinv79, h_v103⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 dropping he_v103 e_v103
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s79 1#u32 (1) (by scalar_tac) hinv79 h64 as ⟨v104, s80, hinv80, h_v104⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v103 dropping
          step as ⟨e_v105, he_v105⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s80 e_v105 (by rw [he_v105]; rfl) h_v104 hinv80 h64 as ⟨v105, s81, hinv81, h_v105⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v103 dropping h_v104 he_v105 e_v105 v104
          store_step with Store.apply_rep s81 v105 v9 _ _ hinv81 h64 h_v105 h_v9 (by ns_tac) (by ns_tac) as ⟨v106, s82, hinv82, h_v106⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v103 dropping h_v105 v105
          store_step with Store.apply_rep s82 v103 v106 _ _ hinv82 h64 h_v103 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s83, hinv83, h_v107⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 dropping h_v103 h_v106 v103 v106
          step as ⟨e_v108, he_v108⟩
          store_step with CtorSpec.eo_bvmul.construct s83 e_v108 (by rw [he_v108]; exact empty_args) hinv83 h64 as ⟨v108, s84, hinv84, h_v108⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v107 dropping he_v108 e_v108
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s84 1#u32 (1) (by scalar_tac) hinv84 h64 as ⟨v109, s85, hinv85, h_v109⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v107 h_v108 dropping
          step as ⟨e_v110, he_v110⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s85 e_v110 (by rw [he_v110]; rfl) h_v109 hinv85 h64 as ⟨v110, s86, hinv86, h_v110⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v107 h_v108 dropping h_v109 he_v110 e_v110 v109
          store_step with Store.apply_rep s86 v110 v12 _ _ hinv86 h64 h_v110 h_v12 (by ns_tac) (by ns_tac) as ⟨v111, s87, hinv87, h_v111⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v107 h_v108 dropping h_v110 v110
          store_step with ih.eo__24eo_5ftypeof s87 v111 _ hinv87 h64 (hG.rem hrem) h_v111 as ⟨v112, s88, hinv88, h_v112⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v107 h_v108 dropping h_v111 v111
          store_step with ih.eo__24eo_5fnil s88 v108 v112 _ _ hinv88 h64 (hG.rem hrem) h_v108 h_v112 as ⟨v113, s89, hinv89, h_v113⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 h_v107 dropping h_v108 h_v112 v108 v112
          store_step with Store.apply_mk_rep s89 v107 v113 _ _ hinv89 h64 h_v107 h_v113 as ⟨v114, s90, hinv90, h_v114⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 h_v102 dropping h_v107 h_v113 v107 v113
          store_step with Store.apply_mk_rep s90 v102 v114 _ _ hinv90 h64 h_v102 h_v114 as ⟨v115, s91, hinv91, h_v115⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 h_v97 dropping h_v102 h_v114 v102 v114
          store_step with Store.apply_mk_rep s91 v97 v115 _ _ hinv91 h64 h_v97 h_v115 as ⟨v116, s92, hinv92, h_v116⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 dropping h_v115 h_v97 v115 v97
          store_step with ih.eo__24eo_5ftypeof s92 v116 _ hinv92 h64 (hG.rem hrem) h_v116 as ⟨v117, s93, hinv93, h_v117⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 h_v92 dropping h_v116 v116
          store_step with ih.eo__24eo_5fnil s93 v92 v117 _ _ hinv93 h64 (hG.rem hrem) h_v92 h_v117 as ⟨v118, s94, hinv94, h_v118⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 h_v91 dropping h_v117 h_v92 v117 v92
          store_step with Store.apply_mk_rep s94 v91 v118 _ _ hinv94 h64 h_v91 h_v118 as ⟨v119, s95, hinv95, h_v119⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 h_v61 dropping h_v118 h_v91 v118 v91
          store_step with Store.apply_mk_rep s95 v61 v119 _ _ hinv95 h64 h_v61 h_v119 as ⟨v120, s96, hinv96, h_v120⟩ growing hG carrying h_v2 h_v9 h_v12 h_v35 dropping h_v119 h_v61 v119 v61
          store_step with Store.apply_mk_rep s96 v35 v120 _ _ hinv96 h64 h_v35 h_v120 as ⟨v121, s97, hinv97, h_v121⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v120 h_v35 v120 v35
          try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
          store_step with Store.literal_binary_u32_spec s97 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv97 h64 as ⟨v122, s98, hinv98, h_v122⟩ growing hG carrying h_v2 h_v9 h_v12 h_v121 dropping
          store_step with Store.apply_mk_rep s98 v121 v122 _ _ hinv98 h64 h_v121 h_v122 as ⟨v123, s99, hinv99, h_v123⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v121 h_v122 v121 v122
          ite_done hinv99 hG with (eo_ite_true_rep _ hx_35 h_v123)
        · ite_branch hbv_35
          step as ⟨e_v124, he_v124⟩
          store_step with CtorSpec.eo__3d.construct s10 e_v124 (by rw [he_v124]; exact empty_args) hinv10 h64 as ⟨v124, s11, hinv11, h_v124⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v34 he_v124 e_v124 v34
          step as ⟨e_v125, he_v125⟩
          store_step with CtorSpec.eo_bvor.construct s11 e_v125 (by rw [he_v125]; exact empty_args) hinv11 h64 as ⟨v125, s12, hinv12, h_v125⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 dropping he_v125 e_v125
          step as ⟨e_v126, he_v126⟩
          store_step with CtorSpec.eo_bvxor.construct s12 e_v126 (by rw [he_v126]; exact empty_args) hinv12 h64 as ⟨v126, s13, hinv13, h_v126⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 dropping he_v126 e_v126
          store_step with Store.apply_rep s13 v126 v12 _ _ hinv13 h64 h_v126 h_v12 (by ns_tac) (by ns_tac) as ⟨v127, s14, hinv14, h_v127⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 dropping h_v126 v126
          step as ⟨e_v128, he_v128⟩
          store_step with CtorSpec.eo_bvxor.construct s14 e_v128 (by rw [he_v128]; exact empty_args) hinv14 h64 as ⟨v128, s15, hinv15, h_v128⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 dropping he_v128 e_v128
          store_step with ih.eo__24eo_5ftypeof s15 v12 _ hinv15 h64 (hG.rem hrem) h_v12 as ⟨v129, s16, hinv16, h_v129⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 dropping hinv15 s15
          store_step with ih.eo__24bv_5fbitwidth s16 v129 _ hinv16 h64 (hG.rem hrem) h_v129 as ⟨v130, s17, hinv17, h_v130⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 dropping h_v129 hinv16 s16 v129
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s17 1#u32 (-1) (by scalar_tac) hinv17 h64 as ⟨v131, s18, hinv18, h_v131⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v130 dropping hinv17 s17
          step as ⟨e_v132, he_v132⟩
          store_step with Store.builtin_spec_add s18 e_v132 (by rw [he_v132]; rfl) h_v130 h_v131 hinv18 h64 as ⟨v132, s19, hinv19, h_v132⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 dropping h_v130 h_v131 he_v132 hinv18 e_v132 s18 v130 v131
          step as ⟨e_v133, he_v133⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s19 e_v133 (by rw [he_v133]; rfl) h_v132 hinv19 h64 as ⟨v133, s20, hinv20, h_v133⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 dropping h_v132 he_v133 hinv19 e_v133 s19 v132
          store_step with ih.eo__24eo_5ftypeof s20 v12 _ hinv20 h64 (hG.rem hrem) h_v12 as ⟨v134, s21, hinv21, h_v134⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 dropping hinv20 s20
          store_step with ih.eo__24bv_5fbitwidth s21 v134 _ hinv21 h64 (hG.rem hrem) h_v134 as ⟨v135, s22, hinv22, h_v135⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 dropping h_v134 hinv21 s21 v134
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s22 1#u32 (-1) (by scalar_tac) hinv22 h64 as ⟨v136, s23, hinv23, h_v136⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 h_v135 dropping hinv22 s22
          step as ⟨e_v137, he_v137⟩
          store_step with Store.builtin_spec_add s23 e_v137 (by rw [he_v137]; rfl) h_v135 h_v136 hinv23 h64 as ⟨v137, s24, hinv24, h_v137⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 dropping h_v135 h_v136 he_v137 hinv23 e_v137 s23 v135 v136
          store_step with ih.eo__24eo_5ftypeof s24 v12 _ hinv24 h64 (hG.rem hrem) h_v12 as ⟨v138, s25, hinv25, h_v138⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 h_v137 dropping hinv24 s24
          store_step with ih.eo__24bv_5fbitwidth s25 v138 _ hinv25 h64 (hG.rem hrem) h_v138 as ⟨v139, s26, hinv26, h_v139⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 h_v137 dropping h_v138 hinv25 s25 v138
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s26 1#u32 (-1) (by scalar_tac) hinv26 h64 as ⟨v140, s27, hinv27, h_v140⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 h_v137 h_v139 dropping hinv26 s26
          step as ⟨e_v141, he_v141⟩
          store_step with Store.builtin_spec_add s27 e_v141 (by rw [he_v141]; rfl) h_v139 h_v140 hinv27 h64 as ⟨v141, s28, hinv28, h_v141⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 h_v137 dropping h_v139 h_v140 he_v141 hinv27 e_v141 s27 v139 v140
          step as ⟨e_v142, he_v142⟩
          store_step with CtorSpec.eo_extract.construct s28 e_v142 (by rw [he_v142]; rfl) h_v137 h_v141 hinv28 h64 as ⟨v142, s29, hinv29, h_v142⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 dropping h_v137 h_v141 he_v142 hinv28 e_v142 s28 v137 v141
          store_step with Store.apply_mk_rep s29 v142 v12 _ _ hinv29 h64 h_v142 h_v12 as ⟨v143, s30, hinv30, h_v143⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 h_v133 dropping h_v142 hinv29 s29 v142
          store_step with Store.apply_mk_rep s30 v133 v143 _ _ hinv30 h64 h_v133 h_v143 as ⟨v144, s31, hinv31, h_v144⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v128 dropping h_v133 h_v143 hinv30 s30 v133 v143
          store_step with Store.apply_mk_rep s31 v128 v144 _ _ hinv31 h64 h_v128 h_v144 as ⟨v145, s32, hinv32, h_v145⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 dropping h_v128 h_v144 hinv31 s31 v128 v144
          step as ⟨e_v146, he_v146⟩
          store_step with CtorSpec.eo_bvxor.construct s32 e_v146 (by rw [he_v146]; exact empty_args) hinv32 h64 as ⟨v146, s33, hinv33, h_v146⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v145 dropping he_v146 hinv32 e_v146 s32
          store_step with ih.eo__24eo_5ftypeof s33 v12 _ hinv33 h64 (hG.rem hrem) h_v12 as ⟨v147, s34, hinv34, h_v147⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v145 h_v146 dropping hinv33 s33
          store_step with ih.eo__24eo_5fnil s34 v146 v147 _ _ hinv34 h64 (hG.rem hrem) h_v146 h_v147 as ⟨v148, s35, hinv35, h_v148⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 h_v145 dropping h_v146 h_v147 hinv34 s34 v146 v147
          store_step with Store.apply_mk_rep s35 v145 v148 _ _ hinv35 h64 h_v145 h_v148 as ⟨v149, s36, hinv36, h_v149⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v127 dropping h_v145 h_v148 hinv35 s35 v145 v148
          store_step with Store.apply_mk_rep s36 v127 v149 _ _ hinv36 h64 h_v127 h_v149 as ⟨v150, s37, hinv37, h_v150⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 dropping h_v127 h_v149 hinv36 s36 v127 v149
          step as ⟨e_v151, he_v151⟩
          store_step with CtorSpec.eo_bvxor.construct s37 e_v151 (by rw [he_v151]; exact empty_args) hinv37 h64 as ⟨v151, s38, hinv38, h_v151⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 dropping he_v151 hinv37 e_v151 s37
          store_step with Store.apply_rep s38 v151 v9 _ _ hinv38 h64 h_v151 h_v9 (by ns_tac) (by ns_tac) as ⟨v152, s39, hinv39, h_v152⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 dropping h_v151 hinv38 s38 v151
          step as ⟨e_v153, he_v153⟩
          store_step with CtorSpec.eo_bvxor.construct s39 e_v153 (by rw [he_v153]; exact empty_args) hinv39 h64 as ⟨v153, s40, hinv40, h_v153⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 dropping he_v153 hinv39 e_v153 s39
          store_step with ih.eo__24eo_5ftypeof s40 v12 _ hinv40 h64 (hG.rem hrem) h_v12 as ⟨v154, s41, hinv41, h_v154⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 dropping hinv40 s40
          store_step with ih.eo__24bv_5fbitwidth s41 v154 _ hinv41 h64 (hG.rem hrem) h_v154 as ⟨v155, s42, hinv42, h_v155⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 dropping h_v154 hinv41 s41 v154
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s42 1#u32 (-1) (by scalar_tac) hinv42 h64 as ⟨v156, s43, hinv43, h_v156⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v155 dropping hinv42 s42
          step as ⟨e_v157, he_v157⟩
          store_step with Store.builtin_spec_add s43 e_v157 (by rw [he_v157]; rfl) h_v155 h_v156 hinv43 h64 as ⟨v157, s44, hinv44, h_v157⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 dropping h_v155 h_v156 he_v157 hinv43 e_v157 s43 v155 v156
          step as ⟨e_v158, he_v158⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s44 e_v158 (by rw [he_v158]; rfl) h_v157 hinv44 h64 as ⟨v158, s45, hinv45, h_v158⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 dropping h_v157 he_v158 hinv44 e_v158 s44 v157
          store_step with ih.eo__24eo_5ftypeof s45 v12 _ hinv45 h64 (hG.rem hrem) h_v12 as ⟨v159, s46, hinv46, h_v159⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 dropping hinv45 s45
          store_step with ih.eo__24bv_5fbitwidth s46 v159 _ hinv46 h64 (hG.rem hrem) h_v159 as ⟨v160, s47, hinv47, h_v160⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 dropping h_v159 hinv46 s46 v159
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s47 1#u32 (-1) (by scalar_tac) hinv47 h64 as ⟨v161, s48, hinv48, h_v161⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 h_v160 dropping hinv47 s47
          step as ⟨e_v162, he_v162⟩
          store_step with Store.builtin_spec_add s48 e_v162 (by rw [he_v162]; rfl) h_v160 h_v161 hinv48 h64 as ⟨v162, s49, hinv49, h_v162⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 dropping h_v160 h_v161 he_v162 hinv48 e_v162 s48 v160 v161
          store_step with ih.eo__24eo_5ftypeof s49 v12 _ hinv49 h64 (hG.rem hrem) h_v12 as ⟨v163, s50, hinv50, h_v163⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 h_v162 dropping hinv49 s49
          store_step with ih.eo__24bv_5fbitwidth s50 v163 _ hinv50 h64 (hG.rem hrem) h_v163 as ⟨v164, s51, hinv51, h_v164⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 h_v162 dropping h_v163 hinv50 s50 v163
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s51 1#u32 (-1) (by scalar_tac) hinv51 h64 as ⟨v165, s52, hinv52, h_v165⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 h_v162 h_v164 dropping hinv51 s51
          step as ⟨e_v166, he_v166⟩
          store_step with Store.builtin_spec_add s52 e_v166 (by rw [he_v166]; rfl) h_v164 h_v165 hinv52 h64 as ⟨v166, s53, hinv53, h_v166⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 h_v162 dropping h_v164 h_v165 he_v166 hinv52 e_v166 s52 v164 v165
          step as ⟨e_v167, he_v167⟩
          store_step with CtorSpec.eo_extract.construct s53 e_v167 (by rw [he_v167]; rfl) h_v162 h_v166 hinv53 h64 as ⟨v167, s54, hinv54, h_v167⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 dropping h_v162 h_v166 he_v167 hinv53 e_v167 s53 v162 v166
          store_step with Store.apply_mk_rep s54 v167 v9 _ _ hinv54 h64 h_v167 h_v9 as ⟨v168, s55, hinv55, h_v168⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 h_v158 dropping h_v167 hinv54 s54 v167
          store_step with Store.apply_mk_rep s55 v158 v168 _ _ hinv55 h64 h_v158 h_v168 as ⟨v169, s56, hinv56, h_v169⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v153 dropping h_v158 h_v168 hinv55 s55 v158 v168
          store_step with Store.apply_mk_rep s56 v153 v169 _ _ hinv56 h64 h_v153 h_v169 as ⟨v170, s57, hinv57, h_v170⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 dropping h_v153 h_v169 hinv56 s56 v153 v169
          step as ⟨e_v171, he_v171⟩
          store_step with CtorSpec.eo_bvxor.construct s57 e_v171 (by rw [he_v171]; exact empty_args) hinv57 h64 as ⟨v171, s58, hinv58, h_v171⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v170 dropping he_v171 hinv57 e_v171 s57
          store_step with ih.eo__24eo_5ftypeof s58 v9 _ hinv58 h64 (hG.rem hrem) h_v9 as ⟨v172, s59, hinv59, h_v172⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v170 h_v171 dropping hinv58 s58
          store_step with ih.eo__24eo_5fnil s59 v171 v172 _ _ hinv59 h64 (hG.rem hrem) h_v171 h_v172 as ⟨v173, s60, hinv60, h_v173⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 h_v170 dropping h_v171 h_v172 hinv59 s59 v171 v172
          store_step with Store.apply_mk_rep s60 v170 v173 _ _ hinv60 h64 h_v170 h_v173 as ⟨v174, s61, hinv61, h_v174⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v152 dropping h_v170 h_v173 hinv60 s60 v170 v173
          store_step with Store.apply_mk_rep s61 v152 v174 _ _ hinv61 h64 h_v152 h_v174 as ⟨v175, s62, hinv62, h_v175⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 dropping h_v152 h_v174 hinv61 s61 v152 v174
          store_step with ih.eo__24eo_5ftypeof s62 v12 _ hinv62 h64 (hG.rem hrem) h_v12 as ⟨v176, s63, hinv63, h_v176⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 dropping hinv62 s62
          store_step with ih.eo__24bv_5fbitwidth s63 v176 _ hinv63 h64 (hG.rem hrem) h_v176 as ⟨v177, s64, hinv64, h_v177⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 dropping h_v176 hinv63 s63 v176
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s64 2#u32 (-2) (by scalar_tac) hinv64 h64 as ⟨v178, s65, hinv65, h_v178⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v177 dropping hinv64 s64
          step as ⟨e_v179, he_v179⟩
          store_step with Store.builtin_spec_add s65 e_v179 (by rw [he_v179]; rfl) h_v177 h_v178 hinv65 h64 as ⟨v179, s66, hinv66, h_v179⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 dropping h_v177 h_v178 he_v179 hinv65 e_v179 s65 v177 v178
          store_step with ih.eo__24eo_5ftypeof s66 v12 _ hinv66 h64 (hG.rem hrem) h_v12 as ⟨v180, s67, hinv67, h_v180⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v179 dropping hinv66 s66
          store_step with ih.eo__24bv_5fbitwidth s67 v180 _ hinv67 h64 (hG.rem hrem) h_v180 as ⟨v181, s68, hinv68, h_v181⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v179 dropping h_v180 hinv67 s67 v180
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s68 2#u32 (-2) (by scalar_tac) hinv68 h64 as ⟨v182, s69, hinv69, h_v182⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v179 h_v181 dropping hinv68 s68
          step as ⟨e_v183, he_v183⟩
          store_step with Store.builtin_spec_add s69 e_v183 (by rw [he_v183]; rfl) h_v181 h_v182 hinv69 h64 as ⟨v183, s70, hinv70, h_v183⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v179 dropping h_v181 h_v182 he_v183 hinv69 e_v183 s69 v181 v182
          step as ⟨e_v184, he_v184⟩
          store_step with CtorSpec.eo_extract.construct s70 e_v184 (by rw [he_v184]; rfl) h_v179 h_v183 hinv70 h64 as ⟨v184, s71, hinv71, h_v184⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 dropping h_v179 h_v183 he_v184 hinv70 e_v184 s70 v179 v183
          step as ⟨e_v185, he_v185⟩
          store_step with CtorSpec.eo_bvxor.construct s71 e_v185 (by rw [he_v185]; exact empty_args) hinv71 h64 as ⟨v185, s72, hinv72, h_v185⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 dropping he_v185 hinv71 e_v185 s71
          store_step with Store.apply_rep s72 v185 v12 _ _ hinv72 h64 h_v185 h_v12 (by ns_tac) (by ns_tac) as ⟨v186, s73, hinv73, h_v186⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 dropping h_v185 hinv72 s72 v185
          step as ⟨e_v187, he_v187⟩
          store_step with CtorSpec.eo_bvxor.construct s73 e_v187 (by rw [he_v187]; exact empty_args) hinv73 h64 as ⟨v187, s74, hinv74, h_v187⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 dropping he_v187 hinv73 e_v187 s73
          store_step with ih.eo__24eo_5ftypeof s74 v12 _ hinv74 h64 (hG.rem hrem) h_v12 as ⟨v188, s75, hinv75, h_v188⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 dropping hinv74 s74
          store_step with ih.eo__24bv_5fbitwidth s75 v188 _ hinv75 h64 (hG.rem hrem) h_v188 as ⟨v189, s76, hinv76, h_v189⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 dropping h_v188 hinv75 s75 v188
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s76 1#u32 (-1) (by scalar_tac) hinv76 h64 as ⟨v190, s77, hinv77, h_v190⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v189 dropping hinv76 s76
          step as ⟨e_v191, he_v191⟩
          store_step with Store.builtin_spec_add s77 e_v191 (by rw [he_v191]; rfl) h_v189 h_v190 hinv77 h64 as ⟨v191, s78, hinv78, h_v191⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 dropping h_v189 h_v190 he_v191 hinv77 e_v191 s77 v189 v190
          step as ⟨e_v192, he_v192⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s78 e_v192 (by rw [he_v192]; rfl) h_v191 hinv78 h64 as ⟨v192, s79, hinv79, h_v192⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 dropping h_v191 he_v192 hinv78 e_v192 s78 v191
          store_step with ih.eo__24eo_5ftypeof s79 v12 _ hinv79 h64 (hG.rem hrem) h_v12 as ⟨v193, s80, hinv80, h_v193⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 dropping hinv79 s79
          store_step with ih.eo__24bv_5fbitwidth s80 v193 _ hinv80 h64 (hG.rem hrem) h_v193 as ⟨v194, s81, hinv81, h_v194⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 dropping h_v193 hinv80 s80 v193
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s81 1#u32 (-1) (by scalar_tac) hinv81 h64 as ⟨v195, s82, hinv82, h_v195⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 h_v194 dropping hinv81 s81
          step as ⟨e_v196, he_v196⟩
          store_step with Store.builtin_spec_add s82 e_v196 (by rw [he_v196]; rfl) h_v194 h_v195 hinv82 h64 as ⟨v196, s83, hinv83, h_v196⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 dropping h_v194 h_v195 he_v196 hinv82 e_v196 s82 v194 v195
          store_step with ih.eo__24eo_5ftypeof s83 v12 _ hinv83 h64 (hG.rem hrem) h_v12 as ⟨v197, s84, hinv84, h_v197⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 h_v196 dropping hinv83 s83
          store_step with ih.eo__24bv_5fbitwidth s84 v197 _ hinv84 h64 (hG.rem hrem) h_v197 as ⟨v198, s85, hinv85, h_v198⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 h_v196 dropping h_v197 hinv84 s84 v197
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s85 1#u32 (-1) (by scalar_tac) hinv85 h64 as ⟨v199, s86, hinv86, h_v199⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 h_v196 h_v198 dropping hinv85 s85
          step as ⟨e_v200, he_v200⟩
          store_step with Store.builtin_spec_add s86 e_v200 (by rw [he_v200]; rfl) h_v198 h_v199 hinv86 h64 as ⟨v200, s87, hinv87, h_v200⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 h_v196 dropping h_v198 h_v199 he_v200 hinv86 e_v200 s86 v198 v199
          step as ⟨e_v201, he_v201⟩
          store_step with CtorSpec.eo_extract.construct s87 e_v201 (by rw [he_v201]; rfl) h_v196 h_v200 hinv87 h64 as ⟨v201, s88, hinv88, h_v201⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 dropping h_v196 h_v200 he_v201 hinv87 e_v201 s87 v196 v200
          store_step with Store.apply_mk_rep s88 v201 v12 _ _ hinv88 h64 h_v201 h_v12 as ⟨v202, s89, hinv89, h_v202⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 h_v192 dropping h_v201 hinv88 s88 v201
          store_step with Store.apply_mk_rep s89 v192 v202 _ _ hinv89 h64 h_v192 h_v202 as ⟨v203, s90, hinv90, h_v203⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v187 dropping h_v192 h_v202 hinv89 s89 v192 v202
          store_step with Store.apply_mk_rep s90 v187 v203 _ _ hinv90 h64 h_v187 h_v203 as ⟨v204, s91, hinv91, h_v204⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 dropping h_v187 h_v203 hinv90 s90 v187 v203
          step as ⟨e_v205, he_v205⟩
          store_step with CtorSpec.eo_bvxor.construct s91 e_v205 (by rw [he_v205]; exact empty_args) hinv91 h64 as ⟨v205, s92, hinv92, h_v205⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v204 dropping he_v205 hinv91 e_v205 s91
          store_step with ih.eo__24eo_5ftypeof s92 v12 _ hinv92 h64 (hG.rem hrem) h_v12 as ⟨v206, s93, hinv93, h_v206⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v204 h_v205 dropping hinv92 s92
          store_step with ih.eo__24eo_5fnil s93 v205 v206 _ _ hinv93 h64 (hG.rem hrem) h_v205 h_v206 as ⟨v207, s94, hinv94, h_v207⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 h_v204 dropping h_v205 h_v206 hinv93 s93 v205 v206
          store_step with Store.apply_mk_rep s94 v204 v207 _ _ hinv94 h64 h_v204 h_v207 as ⟨v208, s95, hinv95, h_v208⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 h_v186 dropping h_v204 h_v207 hinv94 s94 v204 v207
          store_step with Store.apply_mk_rep s95 v186 v208 _ _ hinv95 h64 h_v186 h_v208 as ⟨v209, s96, hinv96, h_v209⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v184 dropping h_v186 h_v208 hinv95 s95 v186 v208
          store_step with Store.apply_mk_rep s96 v184 v209 _ _ hinv96 h64 h_v184 h_v209 as ⟨v210, s97, hinv97, h_v210⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 dropping h_v184 h_v209 hinv96 s96 v184 v209
          step as ⟨e_v211, he_v211⟩
          store_step with CtorSpec.eo_bvand.construct s97 e_v211 (by rw [he_v211]; exact empty_args) hinv97 h64 as ⟨v211, s98, hinv98, h_v211⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 dropping he_v211 hinv97 e_v211 s97
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s98 1#u32 (1) (by scalar_tac) hinv98 h64 as ⟨v212, s99, hinv99, h_v212⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 dropping hinv98 s98
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s99 1#u32 (1) (by scalar_tac) hinv99 h64 as ⟨v213, s100, hinv100, h_v213⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v212 dropping hinv99 s99
          step as ⟨e_v214, he_v214⟩
          store_step with CtorSpec.eo_extract.construct s100 e_v214 (by rw [he_v214]; rfl) h_v212 h_v213 hinv100 h64 as ⟨v214, s101, hinv101, h_v214⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 dropping h_v212 h_v213 he_v214 hinv100 e_v214 s100 v212 v213
          step as ⟨e_v215, he_v215⟩
          store_step with CtorSpec.eo_bvxor.construct s101 e_v215 (by rw [he_v215]; exact empty_args) hinv101 h64 as ⟨v215, s102, hinv102, h_v215⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 dropping he_v215 hinv101 e_v215 s101
          store_step with Store.apply_rep s102 v215 v9 _ _ hinv102 h64 h_v215 h_v9 (by ns_tac) (by ns_tac) as ⟨v216, s103, hinv103, h_v216⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 dropping h_v215 hinv102 s102 v215
          step as ⟨e_v217, he_v217⟩
          store_step with CtorSpec.eo_bvxor.construct s103 e_v217 (by rw [he_v217]; exact empty_args) hinv103 h64 as ⟨v217, s104, hinv104, h_v217⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 dropping he_v217 hinv103 e_v217 s103
          store_step with ih.eo__24eo_5ftypeof s104 v12 _ hinv104 h64 (hG.rem hrem) h_v12 as ⟨v218, s105, hinv105, h_v218⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 dropping hinv104 s104
          store_step with ih.eo__24bv_5fbitwidth s105 v218 _ hinv105 h64 (hG.rem hrem) h_v218 as ⟨v219, s106, hinv106, h_v219⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 dropping h_v218 hinv105 s105 v218
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s106 1#u32 (-1) (by scalar_tac) hinv106 h64 as ⟨v220, s107, hinv107, h_v220⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v219 dropping hinv106 s106
          step as ⟨e_v221, he_v221⟩
          store_step with Store.builtin_spec_add s107 e_v221 (by rw [he_v221]; rfl) h_v219 h_v220 hinv107 h64 as ⟨v221, s108, hinv108, h_v221⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 dropping h_v219 h_v220 he_v221 hinv107 e_v221 s107 v219 v220
          step as ⟨e_v222, he_v222⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s108 e_v222 (by rw [he_v222]; rfl) h_v221 hinv108 h64 as ⟨v222, s109, hinv109, h_v222⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 dropping h_v221 he_v222 hinv108 e_v222 s108 v221
          store_step with ih.eo__24eo_5ftypeof s109 v12 _ hinv109 h64 (hG.rem hrem) h_v12 as ⟨v223, s110, hinv110, h_v223⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 dropping hinv109 s109
          store_step with ih.eo__24bv_5fbitwidth s110 v223 _ hinv110 h64 (hG.rem hrem) h_v223 as ⟨v224, s111, hinv111, h_v224⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 dropping h_v223 hinv110 s110 v223
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s111 1#u32 (-1) (by scalar_tac) hinv111 h64 as ⟨v225, s112, hinv112, h_v225⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 h_v224 dropping hinv111 s111
          step as ⟨e_v226, he_v226⟩
          store_step with Store.builtin_spec_add s112 e_v226 (by rw [he_v226]; rfl) h_v224 h_v225 hinv112 h64 as ⟨v226, s113, hinv113, h_v226⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 dropping h_v224 h_v225 he_v226 hinv112 e_v226 s112 v224 v225
          store_step with ih.eo__24eo_5ftypeof s113 v12 _ hinv113 h64 (hG.rem hrem) h_v12 as ⟨v227, s114, hinv114, h_v227⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 h_v226 dropping hinv113 s113
          store_step with ih.eo__24bv_5fbitwidth s114 v227 _ hinv114 h64 (hG.rem hrem) h_v227 as ⟨v228, s115, hinv115, h_v228⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 h_v226 dropping h_v227 hinv114 s114 v227
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s115 1#u32 (-1) (by scalar_tac) hinv115 h64 as ⟨v229, s116, hinv116, h_v229⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 h_v226 h_v228 dropping hinv115 s115
          step as ⟨e_v230, he_v230⟩
          store_step with Store.builtin_spec_add s116 e_v230 (by rw [he_v230]; rfl) h_v228 h_v229 hinv116 h64 as ⟨v230, s117, hinv117, h_v230⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 h_v226 dropping h_v228 h_v229 he_v230 hinv116 e_v230 s116 v228 v229
          step as ⟨e_v231, he_v231⟩
          store_step with CtorSpec.eo_extract.construct s117 e_v231 (by rw [he_v231]; rfl) h_v226 h_v230 hinv117 h64 as ⟨v231, s118, hinv118, h_v231⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 dropping h_v226 h_v230 he_v231 hinv117 e_v231 s117 v226 v230
          store_step with Store.apply_mk_rep s118 v231 v9 _ _ hinv118 h64 h_v231 h_v9 as ⟨v232, s119, hinv119, h_v232⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 h_v222 dropping h_v231 hinv118 s118 v231
          store_step with Store.apply_mk_rep s119 v222 v232 _ _ hinv119 h64 h_v222 h_v232 as ⟨v233, s120, hinv120, h_v233⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v217 dropping h_v222 h_v232 hinv119 s119 v222 v232
          store_step with Store.apply_mk_rep s120 v217 v233 _ _ hinv120 h64 h_v217 h_v233 as ⟨v234, s121, hinv121, h_v234⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 dropping h_v217 h_v233 hinv120 s120 v217 v233
          step as ⟨e_v235, he_v235⟩
          store_step with CtorSpec.eo_bvxor.construct s121 e_v235 (by rw [he_v235]; exact empty_args) hinv121 h64 as ⟨v235, s122, hinv122, h_v235⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v234 dropping he_v235 hinv121 e_v235 s121
          store_step with ih.eo__24eo_5ftypeof s122 v9 _ hinv122 h64 (hG.rem hrem) h_v9 as ⟨v236, s123, hinv123, h_v236⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v234 h_v235 dropping hinv122 s122
          store_step with ih.eo__24eo_5fnil s123 v235 v236 _ _ hinv123 h64 (hG.rem hrem) h_v235 h_v236 as ⟨v237, s124, hinv124, h_v237⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 h_v234 dropping h_v235 h_v236 hinv123 s123 v235 v236
          store_step with Store.apply_mk_rep s124 v234 v237 _ _ hinv124 h64 h_v234 h_v237 as ⟨v238, s125, hinv125, h_v238⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 h_v216 dropping h_v234 h_v237 hinv124 s124 v234 v237
          store_step with Store.apply_mk_rep s125 v216 v238 _ _ hinv125 h64 h_v216 h_v238 as ⟨v239, s126, hinv126, h_v239⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 h_v214 dropping h_v216 h_v238 hinv125 s125 v216 v238
          store_step with Store.apply_mk_rep s126 v214 v239 _ _ hinv126 h64 h_v214 h_v239 as ⟨v240, s127, hinv127, h_v240⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v211 dropping h_v214 h_v239 hinv126 s126 v214 v239
          store_step with Store.apply_mk_rep s127 v211 v240 _ _ hinv127 h64 h_v211 h_v240 as ⟨v241, s128, hinv128, h_v241⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 dropping h_v211 h_v240 hinv127 s127 v211 v240
          step as ⟨e_v242, he_v242⟩
          store_step with CtorSpec.eo_bvand.construct s128 e_v242 (by rw [he_v242]; exact empty_args) hinv128 h64 as ⟨v242, s129, hinv129, h_v242⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 dropping he_v242 hinv128 e_v242 s128
          store_step with ih.eo__24eo_5ftypeof s129 v12 _ hinv129 h64 (hG.rem hrem) h_v12 as ⟨v243, s130, hinv130, h_v243⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 dropping hinv129 s129
          store_step with ih.eo__24bv_5fbitwidth s130 v243 _ hinv130 h64 (hG.rem hrem) h_v243 as ⟨v244, s131, hinv131, h_v244⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 dropping h_v243 hinv130 s130 v243
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s131 2#u32 (-2) (by scalar_tac) hinv131 h64 as ⟨v245, s132, hinv132, h_v245⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v244 dropping hinv131 s131
          step as ⟨e_v246, he_v246⟩
          store_step with Store.builtin_spec_add s132 e_v246 (by rw [he_v246]; rfl) h_v244 h_v245 hinv132 h64 as ⟨v246, s133, hinv133, h_v246⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 dropping h_v244 h_v245 he_v246 hinv132 e_v246 s132 v244 v245
          store_step with ih.eo__24eo_5ftypeof s133 v12 _ hinv133 h64 (hG.rem hrem) h_v12 as ⟨v247, s134, hinv134, h_v247⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v246 dropping hinv133 s133
          store_step with ih.eo__24bv_5fbitwidth s134 v247 _ hinv134 h64 (hG.rem hrem) h_v247 as ⟨v248, s135, hinv135, h_v248⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v246 dropping h_v247 hinv134 s134 v247
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s135 2#u32 (-2) (by scalar_tac) hinv135 h64 as ⟨v249, s136, hinv136, h_v249⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v246 h_v248 dropping hinv135 s135
          step as ⟨e_v250, he_v250⟩
          store_step with Store.builtin_spec_add s136 e_v250 (by rw [he_v250]; rfl) h_v248 h_v249 hinv136 h64 as ⟨v250, s137, hinv137, h_v250⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v246 dropping h_v248 h_v249 he_v250 hinv136 e_v250 s136 v248 v249
          step as ⟨e_v251, he_v251⟩
          store_step with CtorSpec.eo_extract.construct s137 e_v251 (by rw [he_v251]; rfl) h_v246 h_v250 hinv137 h64 as ⟨v251, s138, hinv138, h_v251⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 dropping h_v246 h_v250 he_v251 hinv137 e_v251 s137 v246 v250
          step as ⟨e_v252, he_v252⟩
          store_step with CtorSpec.eo_bvxor.construct s138 e_v252 (by rw [he_v252]; exact empty_args) hinv138 h64 as ⟨v252, s139, hinv139, h_v252⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 dropping he_v252 hinv138 e_v252 s138
          store_step with Store.apply_rep s139 v252 v12 _ _ hinv139 h64 h_v252 h_v12 (by ns_tac) (by ns_tac) as ⟨v253, s140, hinv140, h_v253⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 dropping h_v252 hinv139 s139 v252
          step as ⟨e_v254, he_v254⟩
          store_step with CtorSpec.eo_bvxor.construct s140 e_v254 (by rw [he_v254]; exact empty_args) hinv140 h64 as ⟨v254, s141, hinv141, h_v254⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 dropping he_v254 hinv140 e_v254 s140
          store_step with ih.eo__24eo_5ftypeof s141 v12 _ hinv141 h64 (hG.rem hrem) h_v12 as ⟨v255, s142, hinv142, h_v255⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 dropping hinv141 s141
          store_step with ih.eo__24bv_5fbitwidth s142 v255 _ hinv142 h64 (hG.rem hrem) h_v255 as ⟨v256, s143, hinv143, h_v256⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 dropping h_v255 hinv142 s142 v255
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s143 1#u32 (-1) (by scalar_tac) hinv143 h64 as ⟨v257, s144, hinv144, h_v257⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v256 dropping hinv143 s143
          step as ⟨e_v258, he_v258⟩
          store_step with Store.builtin_spec_add s144 e_v258 (by rw [he_v258]; rfl) h_v256 h_v257 hinv144 h64 as ⟨v258, s145, hinv145, h_v258⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 dropping h_v256 h_v257 he_v258 hinv144 e_v258 s144 v256 v257
          step as ⟨e_v259, he_v259⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s145 e_v259 (by rw [he_v259]; rfl) h_v258 hinv145 h64 as ⟨v259, s146, hinv146, h_v259⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 dropping h_v258 he_v259 hinv145 e_v259 s145 v258
          store_step with ih.eo__24eo_5ftypeof s146 v12 _ hinv146 h64 (hG.rem hrem) h_v12 as ⟨v260, s147, hinv147, h_v260⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 dropping hinv146 s146
          store_step with ih.eo__24bv_5fbitwidth s147 v260 _ hinv147 h64 (hG.rem hrem) h_v260 as ⟨v261, s148, hinv148, h_v261⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 dropping h_v260 hinv147 s147 v260
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s148 1#u32 (-1) (by scalar_tac) hinv148 h64 as ⟨v262, s149, hinv149, h_v262⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 h_v261 dropping hinv148 s148
          step as ⟨e_v263, he_v263⟩
          store_step with Store.builtin_spec_add s149 e_v263 (by rw [he_v263]; rfl) h_v261 h_v262 hinv149 h64 as ⟨v263, s150, hinv150, h_v263⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 dropping h_v261 h_v262 he_v263 hinv149 e_v263 s149 v261 v262
          store_step with ih.eo__24eo_5ftypeof s150 v12 _ hinv150 h64 (hG.rem hrem) h_v12 as ⟨v264, s151, hinv151, h_v264⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 h_v263 dropping hinv150 s150
          store_step with ih.eo__24bv_5fbitwidth s151 v264 _ hinv151 h64 (hG.rem hrem) h_v264 as ⟨v265, s152, hinv152, h_v265⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 h_v263 dropping h_v264 hinv151 s151 v264
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s152 1#u32 (-1) (by scalar_tac) hinv152 h64 as ⟨v266, s153, hinv153, h_v266⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 h_v263 h_v265 dropping hinv152 s152
          step as ⟨e_v267, he_v267⟩
          store_step with Store.builtin_spec_add s153 e_v267 (by rw [he_v267]; rfl) h_v265 h_v266 hinv153 h64 as ⟨v267, s154, hinv154, h_v267⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 h_v263 dropping h_v265 h_v266 he_v267 hinv153 e_v267 s153 v265 v266
          step as ⟨e_v268, he_v268⟩
          store_step with CtorSpec.eo_extract.construct s154 e_v268 (by rw [he_v268]; rfl) h_v263 h_v267 hinv154 h64 as ⟨v268, s155, hinv155, h_v268⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 dropping h_v263 h_v267 he_v268 hinv154 e_v268 s154 v263 v267
          store_step with Store.apply_mk_rep s155 v268 v12 _ _ hinv155 h64 h_v268 h_v12 as ⟨v269, s156, hinv156, h_v269⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 h_v259 dropping h_v268 hinv155 s155 v268
          store_step with Store.apply_mk_rep s156 v259 v269 _ _ hinv156 h64 h_v259 h_v269 as ⟨v270, s157, hinv157, h_v270⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v254 dropping h_v259 h_v269 hinv156 s156 v259 v269
          store_step with Store.apply_mk_rep s157 v254 v270 _ _ hinv157 h64 h_v254 h_v270 as ⟨v271, s158, hinv158, h_v271⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 dropping h_v254 h_v270 hinv157 s157 v254 v270
          step as ⟨e_v272, he_v272⟩
          store_step with CtorSpec.eo_bvxor.construct s158 e_v272 (by rw [he_v272]; exact empty_args) hinv158 h64 as ⟨v272, s159, hinv159, h_v272⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v271 dropping he_v272 hinv158 e_v272 s158
          store_step with ih.eo__24eo_5ftypeof s159 v12 _ hinv159 h64 (hG.rem hrem) h_v12 as ⟨v273, s160, hinv160, h_v273⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v271 h_v272 dropping hinv159 s159
          store_step with ih.eo__24eo_5fnil s160 v272 v273 _ _ hinv160 h64 (hG.rem hrem) h_v272 h_v273 as ⟨v274, s161, hinv161, h_v274⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 h_v271 dropping h_v272 h_v273 hinv160 s160 v272 v273
          store_step with Store.apply_mk_rep s161 v271 v274 _ _ hinv161 h64 h_v271 h_v274 as ⟨v275, s162, hinv162, h_v275⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 h_v253 dropping h_v271 h_v274 hinv161 s161 v271 v274
          store_step with Store.apply_mk_rep s162 v253 v275 _ _ hinv162 h64 h_v253 h_v275 as ⟨v276, s163, hinv163, h_v276⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 h_v251 dropping h_v253 h_v275 hinv162 s162 v253 v275
          store_step with Store.apply_mk_rep s163 v251 v276 _ _ hinv163 h64 h_v251 h_v276 as ⟨v277, s164, hinv164, h_v277⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v242 dropping h_v251 h_v276 hinv163 s163 v251 v276
          store_step with Store.apply_mk_rep s164 v242 v277 _ _ hinv164 h64 h_v242 h_v277 as ⟨v278, s165, hinv165, h_v278⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 dropping h_v242 h_v277 hinv164 s164 v242 v277
          step as ⟨e_v279, he_v279⟩
          store_step with CtorSpec.eo_bvand.construct s165 e_v279 (by rw [he_v279]; exact empty_args) hinv165 h64 as ⟨v279, s166, hinv166, h_v279⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 dropping he_v279 hinv165 e_v279 s165
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s166 1#u32 (1) (by scalar_tac) hinv166 h64 as ⟨v280, s167, hinv167, h_v280⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 dropping hinv166 s166
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s167 1#u32 (1) (by scalar_tac) hinv167 h64 as ⟨v281, s168, hinv168, h_v281⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v280 dropping hinv167 s167
          step as ⟨e_v282, he_v282⟩
          store_step with CtorSpec.eo_extract.construct s168 e_v282 (by rw [he_v282]; rfl) h_v280 h_v281 hinv168 h64 as ⟨v282, s169, hinv169, h_v282⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 dropping h_v280 h_v281 he_v282 hinv168 e_v282 s168 v280 v281
          step as ⟨e_v283, he_v283⟩
          store_step with CtorSpec.eo_bvxor.construct s169 e_v283 (by rw [he_v283]; exact empty_args) hinv169 h64 as ⟨v283, s170, hinv170, h_v283⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 dropping he_v283 hinv169 e_v283 s169
          store_step with Store.apply_rep s170 v283 v9 _ _ hinv170 h64 h_v283 h_v9 (by ns_tac) (by ns_tac) as ⟨v284, s171, hinv171, h_v284⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 dropping h_v283 hinv170 s170 v283
          step as ⟨e_v285, he_v285⟩
          store_step with CtorSpec.eo_bvxor.construct s171 e_v285 (by rw [he_v285]; exact empty_args) hinv171 h64 as ⟨v285, s172, hinv172, h_v285⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 dropping he_v285 hinv171 e_v285 s171
          store_step with ih.eo__24eo_5ftypeof s172 v12 _ hinv172 h64 (hG.rem hrem) h_v12 as ⟨v286, s173, hinv173, h_v286⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 dropping hinv172 s172
          store_step with ih.eo__24bv_5fbitwidth s173 v286 _ hinv173 h64 (hG.rem hrem) h_v286 as ⟨v287, s174, hinv174, h_v287⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 dropping h_v286 hinv173 s173 v286
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s174 1#u32 (-1) (by scalar_tac) hinv174 h64 as ⟨v288, s175, hinv175, h_v288⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v287 dropping hinv174 s174
          step as ⟨e_v289, he_v289⟩
          store_step with Store.builtin_spec_add s175 e_v289 (by rw [he_v289]; rfl) h_v287 h_v288 hinv175 h64 as ⟨v289, s176, hinv176, h_v289⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 dropping h_v287 h_v288 he_v289 hinv175 e_v289 s175 v287 v288
          step as ⟨e_v290, he_v290⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s176 e_v290 (by rw [he_v290]; rfl) h_v289 hinv176 h64 as ⟨v290, s177, hinv177, h_v290⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 dropping h_v289 he_v290 hinv176 e_v290 s176 v289
          store_step with ih.eo__24eo_5ftypeof s177 v12 _ hinv177 h64 (hG.rem hrem) h_v12 as ⟨v291, s178, hinv178, h_v291⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 dropping hinv177 s177
          store_step with ih.eo__24bv_5fbitwidth s178 v291 _ hinv178 h64 (hG.rem hrem) h_v291 as ⟨v292, s179, hinv179, h_v292⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 dropping h_v291 hinv178 s178 v291
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s179 1#u32 (-1) (by scalar_tac) hinv179 h64 as ⟨v293, s180, hinv180, h_v293⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 h_v292 dropping hinv179 s179
          step as ⟨e_v294, he_v294⟩
          store_step with Store.builtin_spec_add s180 e_v294 (by rw [he_v294]; rfl) h_v292 h_v293 hinv180 h64 as ⟨v294, s181, hinv181, h_v294⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 dropping h_v292 h_v293 he_v294 hinv180 e_v294 s180 v292 v293
          store_step with ih.eo__24eo_5ftypeof s181 v12 _ hinv181 h64 (hG.rem hrem) h_v12 as ⟨v295, s182, hinv182, h_v295⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 h_v294 dropping hinv181 s181
          store_step with ih.eo__24bv_5fbitwidth s182 v295 _ hinv182 h64 (hG.rem hrem) h_v295 as ⟨v296, s183, hinv183, h_v296⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 h_v294 dropping h_v295 hinv182 s182 v295
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s183 1#u32 (-1) (by scalar_tac) hinv183 h64 as ⟨v297, s184, hinv184, h_v297⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 h_v294 h_v296 dropping hinv183 s183
          step as ⟨e_v298, he_v298⟩
          store_step with Store.builtin_spec_add s184 e_v298 (by rw [he_v298]; rfl) h_v296 h_v297 hinv184 h64 as ⟨v298, s185, hinv185, h_v298⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 h_v294 dropping h_v296 h_v297 he_v298 hinv184 e_v298 s184 v296 v297
          step as ⟨e_v299, he_v299⟩
          store_step with CtorSpec.eo_extract.construct s185 e_v299 (by rw [he_v299]; rfl) h_v294 h_v298 hinv185 h64 as ⟨v299, s186, hinv186, h_v299⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 dropping h_v294 h_v298 he_v299 hinv185 e_v299 s185 v294 v298
          store_step with Store.apply_mk_rep s186 v299 v9 _ _ hinv186 h64 h_v299 h_v9 as ⟨v300, s187, hinv187, h_v300⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 h_v290 dropping h_v299 hinv186 s186 v299
          store_step with Store.apply_mk_rep s187 v290 v300 _ _ hinv187 h64 h_v290 h_v300 as ⟨v301, s188, hinv188, h_v301⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v285 dropping h_v290 h_v300 hinv187 s187 v290 v300
          store_step with Store.apply_mk_rep s188 v285 v301 _ _ hinv188 h64 h_v285 h_v301 as ⟨v302, s189, hinv189, h_v302⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 dropping h_v285 h_v301 hinv188 s188 v285 v301
          step as ⟨e_v303, he_v303⟩
          store_step with CtorSpec.eo_bvxor.construct s189 e_v303 (by rw [he_v303]; exact empty_args) hinv189 h64 as ⟨v303, s190, hinv190, h_v303⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v302 dropping he_v303 hinv189 e_v303 s189
          store_step with ih.eo__24eo_5ftypeof s190 v9 _ hinv190 h64 (hG.rem hrem) h_v9 as ⟨v304, s191, hinv191, h_v304⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v302 h_v303 dropping hinv190 s190
          store_step with ih.eo__24eo_5fnil s191 v303 v304 _ _ hinv191 h64 (hG.rem hrem) h_v303 h_v304 as ⟨v305, s192, hinv192, h_v305⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 h_v302 dropping h_v303 h_v304 hinv191 s191 v303 v304
          store_step with Store.apply_mk_rep s192 v302 v305 _ _ hinv192 h64 h_v302 h_v305 as ⟨v306, s193, hinv193, h_v306⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 h_v284 dropping h_v302 h_v305 hinv192 s192 v302 v305
          store_step with Store.apply_mk_rep s193 v284 v306 _ _ hinv193 h64 h_v284 h_v306 as ⟨v307, s194, hinv194, h_v307⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 h_v282 dropping h_v284 h_v306 hinv193 s193 v284 v306
          store_step with Store.apply_mk_rep s194 v282 v307 _ _ hinv194 h64 h_v282 h_v307 as ⟨v308, s195, hinv195, h_v308⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 dropping h_v282 h_v307 hinv194 s194 v282 v307
          store_step with ih.eo__24eo_5ftypeof s195 v308 _ hinv195 h64 (hG.rem hrem) h_v308 as ⟨v309, s196, hinv196, h_v309⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 h_v279 dropping h_v308 hinv195 s195 v308
          store_step with ih.eo__24eo_5fnil s196 v279 v309 _ _ hinv196 h64 (hG.rem hrem) h_v279 h_v309 as ⟨v310, s197, hinv197, h_v310⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 h_v278 dropping h_v279 h_v309 hinv196 s196 v279 v309
          store_step with Store.apply_mk_rep s197 v278 v310 _ _ hinv197 h64 h_v278 h_v310 as ⟨v311, s198, hinv198, h_v311⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v241 dropping h_v278 h_v310 hinv197 s197 v278 v310
          store_step with Store.apply_mk_rep s198 v241 v311 _ _ hinv198 h64 h_v241 h_v311 as ⟨v312, s199, hinv199, h_v312⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 dropping h_v241 h_v311 hinv198 s198 v241 v311
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s199 1#u32 (1) (by scalar_tac) hinv199 h64 as ⟨v313, s200, hinv200, h_v313⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping hinv199 s199
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s200 1#u32 (-1) (by scalar_tac) hinv200 h64 as ⟨v314, s201, hinv201, h_v314⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v313 dropping hinv200 s200
          store_step with ih.eo__24eo_5ftypeof s201 v12 _ hinv201 h64 (hG.rem hrem) h_v12 as ⟨v315, s202, hinv202, h_v315⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v313 h_v314 dropping hinv201 s201
          store_step with ih.eo__24bv_5fbitwidth s202 v315 _ hinv202 h64 (hG.rem hrem) h_v315 as ⟨v316, s203, hinv203, h_v316⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v313 h_v314 dropping h_v315 hinv202 s202 v315
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s203 2#u32 (-2) (by scalar_tac) hinv203 h64 as ⟨v317, s204, hinv204, h_v317⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v313 h_v314 h_v316 dropping hinv203 s203
          step as ⟨e_v318, he_v318⟩
          store_step with Store.builtin_spec_add s204 e_v318 (by rw [he_v318]; rfl) h_v316 h_v317 hinv204 h64 as ⟨v318, s205, hinv205, h_v318⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v313 h_v314 dropping h_v316 h_v317 he_v318 hinv204 e_v318 s204 v316 v317
          step as ⟨e_v319, he_v319⟩
          store_step with Store.builtin_spec_add s205 e_v319 (by rw [he_v319]; rfl) h_v314 h_v318 hinv205 h64 as ⟨v319, s206, hinv206, h_v319⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v313 dropping h_v314 h_v318 he_v319 hinv205 e_v319 s205 v314 v318
          step as ⟨e_v320, he_v320⟩
          store_step with Store.builtin_spec_add s206 e_v320 (by rw [he_v320]; rfl) h_v313 h_v319 hinv206 h64 as ⟨v320, s207, hinv207, h_v320⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_v313 h_v319 he_v320 hinv206 e_v320 s206 v313 v319
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s207 1#u32 (-1) (by scalar_tac) hinv207 h64 as ⟨v321, s208, hinv208, h_v321⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v320 dropping hinv207 s207
          step as ⟨e_v322, he_v322⟩
          store_step with Store.builtin_spec_add s208 e_v322 (by rw [he_v322]; rfl) h_v320 h_v321 hinv208 h64 as ⟨v322, s209, hinv209, h_v322⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_v320 h_v321 he_v322 hinv208 e_v322 s208 v320 v321
          step as ⟨e_v323, he_v323⟩
          store_step with Store.builtin_spec_is_neg s209 e_v323 (by rw [he_v323]; rfl) h_v322 hinv209 h64 as ⟨v323, s210, hinv210, h_v323⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_v322 he_v323 hinv209 e_v323 s209 v322
          store_step with Store.literal_boolean_spec s210 false hinv210 h64 as ⟨v324, s211, hinv211, h_v324⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v323 dropping hinv210 s210
          have h_req_v340 := (show requires_1_eo__24eo_5fprog_5fbv_2dsmulo_2delim s211 v323 v324 v12 ⦃ r s' => s'.Inv ∧ s211.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold requires_1_eo__24eo_5fprog_5fbv_2dsmulo_2delim
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s211
            req_same v323 v324 with h_v323 h_v324 using hinv211 hG
            req_stuck h_v323 as hq_v323 using hinv211 hG
            step as ⟨e_v325, he_v325⟩
            store_step with CtorSpec.eo__40_40TypedList_2econs.construct s211 e_v325 (by rw [he_v325]; exact empty_args) hinv211 h64 as ⟨v325, s212, hinv212, h_v325⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_v323 h_v324 he_v325 hinv211 e_v325 s211 v323 v324
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s212 0#u32 (0) (by scalar_tac) hinv212 h64 as ⟨v326, s213, hinv213, h_v326⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 dropping hinv212 s212
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s213 1#u32 (1) (by scalar_tac) hinv213 h64 as ⟨v327, s214, hinv214, h_v327⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 dropping hinv213 s213
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s214 1#u32 (-1) (by scalar_tac) hinv214 h64 as ⟨v328, s215, hinv215, h_v328⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v327 dropping hinv214 s214
            store_step with ih.eo__24eo_5ftypeof s215 v12 _ hinv215 h64 (hG.rem hrem) h_v12 as ⟨v329, s216, hinv216, h_v329⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v327 h_v328 dropping hinv215 s215
            store_step with ih.eo__24bv_5fbitwidth s216 v329 _ hinv216 h64 (hG.rem hrem) h_v329 as ⟨v330, s217, hinv217, h_v330⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v327 h_v328 dropping h_v329 hinv216 s216 v329
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s217 2#u32 (-2) (by scalar_tac) hinv217 h64 as ⟨v331, s218, hinv218, h_v331⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v327 h_v328 h_v330 dropping hinv217 s217
            step as ⟨e_v332, he_v332⟩
            store_step with Store.builtin_spec_add s218 e_v332 (by rw [he_v332]; rfl) h_v330 h_v331 hinv218 h64 as ⟨v332, s219, hinv219, h_v332⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v327 h_v328 dropping h_v330 h_v331 he_v332 hinv218 e_v332 s218 v330 v331
            step as ⟨e_v333, he_v333⟩
            store_step with Store.builtin_spec_add s219 e_v333 (by rw [he_v333]; rfl) h_v328 h_v332 hinv219 h64 as ⟨v333, s220, hinv220, h_v333⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v327 dropping h_v328 h_v332 he_v333 hinv219 e_v333 s219 v328 v332
            step as ⟨e_v334, he_v334⟩
            store_step with Store.builtin_spec_add s220 e_v334 (by rw [he_v334]; rfl) h_v327 h_v333 hinv220 h64 as ⟨v334, s221, hinv221, h_v334⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 dropping h_v327 h_v333 he_v334 hinv220 e_v334 s220 v327 v333
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s221 1#u32 (-1) (by scalar_tac) hinv221 h64 as ⟨v335, s222, hinv222, h_v335⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 h_v334 dropping hinv221 s221
            step as ⟨e_v336, he_v336⟩
            store_step with Store.builtin_spec_add s222 e_v336 (by rw [he_v336]; rfl) h_v334 h_v335 hinv222 h64 as ⟨v336, s223, hinv223, h_v336⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v325 h_v326 dropping h_v334 h_v335 he_v336 hinv222 e_v336 s222 v334 v335
            step as ⟨e_v337, he_v337⟩
            store_step with Store.builtin_spec_list_repeat n ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s223 e_v337 (by rw [he_v337]; rfl) h_v325 h_v326 h_v336 hinv223 h64 (hG.rem hrem) op_not_left_eo__40_40TypedList_2econs as ⟨v337, s224, hinv224, h_v337⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_v325 h_v326 h_v336 he_v337 hinv223 e_v337 s223 v325 v326 v336
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s224 1#u32 (1) (by scalar_tac) hinv224 h64 as ⟨v338, s225, hinv225, h_v338⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v337 dropping hinv224 s224
            store_step with ih.eo__24iota_5frec s225 v337 v338 _ _ hinv225 h64 (hG.rem hrem) h_v337 h_v338 as ⟨v339, s226, hinv226, h_v339⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_v337 h_v338 hinv225 s225 v337 v338
            req_done hinv226 hG with h_v339 using hq_v323)
          store_step with h_req_v340 as ⟨v340, s227, hinv227, h_v340⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 dropping h_req_v340 h_v323 h_v324 hinv211 s211 v323 v324
          store_step with ih.eo__24eo_5ftypeof s227 v12 _ hinv227 h64 (hG.rem hrem) h_v12 as ⟨v341, s228, hinv228, h_v341⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v340 dropping hinv227 s227
          store_step with ih.eo__24bv_5fbitwidth s228 v341 _ hinv228 h64 (hG.rem hrem) h_v341 as ⟨v342, s229, hinv229, h_v342⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v340 dropping h_v341 hinv228 s228 v341
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s229 2#u32 (-2) (by scalar_tac) hinv229 h64 as ⟨v343, s230, hinv230, h_v343⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v340 h_v342 dropping hinv229 s229
          step as ⟨e_v344, he_v344⟩
          store_step with Store.builtin_spec_add s230 e_v344 (by rw [he_v344]; rfl) h_v342 h_v343 hinv230 h64 as ⟨v344, s231, hinv231, h_v344⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 h_v150 h_v175 h_v210 h_v312 h_v340 dropping h_v342 h_v343 he_v344 hinv230 e_v344 s230 v342 v343
          store_step with ih.eo__24bv_5fsmulo_5felim_5frec s231 v150 v175 v210 v312 v340 v344 _ _ _ _ _ _ hinv231 h64 (hG.rem hrem) h_v150 h_v175 h_v210 h_v312 h_v340 h_v344 as ⟨v345, s232, hinv232, h_v345⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v125 dropping h_v150 h_v175 h_v210 h_v312 h_v340 h_v344 hinv231 s231 v150 v175 v210 v312 v340 v344
          store_step with Store.apply_mk_rep s232 v125 v345 _ _ hinv232 h64 h_v125 h_v345 as ⟨v346, s233, hinv233, h_v346⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 dropping h_v125 h_v345 hinv232 s232 v125 v345
          step as ⟨e_v347, he_v347⟩
          store_step with CtorSpec.eo_bvor.construct s233 e_v347 (by rw [he_v347]; exact empty_args) hinv233 h64 as ⟨v347, s234, hinv234, h_v347⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 dropping he_v347 hinv233 e_v347 s233
          step as ⟨e_v348, he_v348⟩
          store_step with CtorSpec.eo_bvxor.construct s234 e_v348 (by rw [he_v348]; exact empty_args) hinv234 h64 as ⟨v348, s235, hinv235, h_v348⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 dropping he_v348 hinv234 e_v348 s234
          store_step with ih.eo__24eo_5ftypeof s235 v12 _ hinv235 h64 (hG.rem hrem) h_v12 as ⟨v349, s236, hinv236, h_v349⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 dropping hinv235 s235
          store_step with ih.eo__24bv_5fbitwidth s236 v349 _ hinv236 h64 (hG.rem hrem) h_v349 as ⟨v350, s237, hinv237, h_v350⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 dropping h_v349 hinv236 s236 v349
          store_step with ih.eo__24eo_5ftypeof s237 v12 _ hinv237 h64 (hG.rem hrem) h_v12 as ⟨v351, s238, hinv238, h_v351⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v350 dropping hinv237 s237
          store_step with ih.eo__24bv_5fbitwidth s238 v351 _ hinv238 h64 (hG.rem hrem) h_v351 as ⟨v352, s239, hinv239, h_v352⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v350 dropping h_v351 hinv238 s238 v351
          step as ⟨e_v353, he_v353⟩
          store_step with CtorSpec.eo_extract.construct s239 e_v353 (by rw [he_v353]; rfl) h_v350 h_v352 hinv239 h64 as ⟨v353, s240, hinv240, h_v353⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 dropping h_v350 h_v352 he_v353 hinv239 e_v353 s239 v350 v352
          step as ⟨e_v354, he_v354⟩
          store_step with CtorSpec.eo_bvmul.construct s240 e_v354 (by rw [he_v354]; exact empty_args) hinv240 h64 as ⟨v354, s241, hinv241, h_v354⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 dropping he_v354 hinv240 e_v354 s240
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s241 1#u32 (1) (by scalar_tac) hinv241 h64 as ⟨v355, s242, hinv242, h_v355⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v354 dropping hinv241 s241
          step as ⟨e_v356, he_v356⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s242 e_v356 (by rw [he_v356]; rfl) h_v355 hinv242 h64 as ⟨v356, s243, hinv243, h_v356⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v354 dropping h_v355 he_v356 hinv242 e_v356 s242 v355
          store_step with Store.apply_rep s243 v356 v12 _ _ hinv243 h64 h_v356 h_v12 (by ns_tac) (by ns_tac) as ⟨v357, s244, hinv244, h_v357⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v354 dropping h_v356 hinv243 s243 v356
          store_step with Store.apply_rep s244 v354 v357 _ _ hinv244 h64 h_v354 h_v357 (by ns_tac) (by ns_tac) as ⟨v358, s245, hinv245, h_v358⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 dropping h_v354 h_v357 hinv244 s244 v354 v357
          step as ⟨e_v359, he_v359⟩
          store_step with CtorSpec.eo_bvmul.construct s245 e_v359 (by rw [he_v359]; exact empty_args) hinv245 h64 as ⟨v359, s246, hinv246, h_v359⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 dropping he_v359 hinv245 e_v359 s245
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s246 1#u32 (1) (by scalar_tac) hinv246 h64 as ⟨v360, s247, hinv247, h_v360⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v359 dropping hinv246 s246
          step as ⟨e_v361, he_v361⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s247 e_v361 (by rw [he_v361]; rfl) h_v360 hinv247 h64 as ⟨v361, s248, hinv248, h_v361⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v359 dropping h_v360 he_v361 hinv247 e_v361 s247 v360
          store_step with Store.apply_rep s248 v361 v9 _ _ hinv248 h64 h_v361 h_v9 (by ns_tac) (by ns_tac) as ⟨v362, s249, hinv249, h_v362⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v359 dropping h_v361 hinv248 s248 v361
          store_step with Store.apply_rep s249 v359 v362 _ _ hinv249 h64 h_v359 h_v362 (by ns_tac) (by ns_tac) as ⟨v363, s250, hinv250, h_v363⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 dropping h_v359 h_v362 hinv249 s249 v359 v362
          step as ⟨e_v364, he_v364⟩
          store_step with CtorSpec.eo_bvmul.construct s250 e_v364 (by rw [he_v364]; exact empty_args) hinv250 h64 as ⟨v364, s251, hinv251, h_v364⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v363 dropping he_v364 hinv250 e_v364 s250
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s251 1#u32 (1) (by scalar_tac) hinv251 h64 as ⟨v365, s252, hinv252, h_v365⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v363 h_v364 dropping hinv251 s251
          step as ⟨e_v366, he_v366⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s252 e_v366 (by rw [he_v366]; rfl) h_v365 hinv252 h64 as ⟨v366, s253, hinv253, h_v366⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v363 h_v364 dropping h_v365 he_v366 hinv252 e_v366 s252 v365
          store_step with Store.apply_rep s253 v366 v12 _ _ hinv253 h64 h_v366 h_v12 (by ns_tac) (by ns_tac) as ⟨v367, s254, hinv254, h_v367⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v363 h_v364 dropping h_v366 hinv253 s253 v366
          store_step with ih.eo__24eo_5ftypeof s254 v367 _ hinv254 h64 (hG.rem hrem) h_v367 as ⟨v368, s255, hinv255, h_v368⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v363 h_v364 dropping h_v367 hinv254 s254 v367
          store_step with ih.eo__24eo_5fnil s255 v364 v368 _ _ hinv255 h64 (hG.rem hrem) h_v364 h_v368 as ⟨v369, s256, hinv256, h_v369⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 h_v363 dropping h_v364 h_v368 hinv255 s255 v364 v368
          store_step with Store.apply_mk_rep s256 v363 v369 _ _ hinv256 h64 h_v363 h_v369 as ⟨v370, s257, hinv257, h_v370⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 h_v358 dropping h_v363 h_v369 hinv256 s256 v363 v369
          store_step with Store.apply_mk_rep s257 v358 v370 _ _ hinv257 h64 h_v358 h_v370 as ⟨v371, s258, hinv258, h_v371⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 h_v353 dropping h_v358 h_v370 hinv257 s257 v358 v370
          store_step with Store.apply_mk_rep s258 v353 v371 _ _ hinv258 h64 h_v353 h_v371 as ⟨v372, s259, hinv259, h_v372⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v348 dropping h_v353 h_v371 hinv258 s258 v353 v371
          store_step with Store.apply_mk_rep s259 v348 v372 _ _ hinv259 h64 h_v348 h_v372 as ⟨v373, s260, hinv260, h_v373⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 dropping h_v348 h_v372 hinv259 s259 v348 v372
          step as ⟨e_v374, he_v374⟩
          store_step with CtorSpec.eo_bvxor.construct s260 e_v374 (by rw [he_v374]; exact empty_args) hinv260 h64 as ⟨v374, s261, hinv261, h_v374⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 dropping he_v374 hinv260 e_v374 s260
          store_step with ih.eo__24eo_5ftypeof s261 v12 _ hinv261 h64 (hG.rem hrem) h_v12 as ⟨v375, s262, hinv262, h_v375⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 dropping hinv261 s261
          store_step with ih.eo__24bv_5fbitwidth s262 v375 _ hinv262 h64 (hG.rem hrem) h_v375 as ⟨v376, s263, hinv263, h_v376⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 dropping h_v375 hinv262 s262 v375
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s263 1#u32 (-1) (by scalar_tac) hinv263 h64 as ⟨v377, s264, hinv264, h_v377⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v376 dropping hinv263 s263
          step as ⟨e_v378, he_v378⟩
          store_step with Store.builtin_spec_add s264 e_v378 (by rw [he_v378]; rfl) h_v376 h_v377 hinv264 h64 as ⟨v378, s265, hinv265, h_v378⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 dropping h_v376 h_v377 he_v378 hinv264 e_v378 s264 v376 v377
          store_step with ih.eo__24eo_5ftypeof s265 v12 _ hinv265 h64 (hG.rem hrem) h_v12 as ⟨v379, s266, hinv266, h_v379⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v378 dropping hinv265 s265
          store_step with ih.eo__24bv_5fbitwidth s266 v379 _ hinv266 h64 (hG.rem hrem) h_v379 as ⟨v380, s267, hinv267, h_v380⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v378 dropping h_v379 hinv266 s266 v379
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s267 1#u32 (-1) (by scalar_tac) hinv267 h64 as ⟨v381, s268, hinv268, h_v381⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v378 h_v380 dropping hinv267 s267
          step as ⟨e_v382, he_v382⟩
          store_step with Store.builtin_spec_add s268 e_v382 (by rw [he_v382]; rfl) h_v380 h_v381 hinv268 h64 as ⟨v382, s269, hinv269, h_v382⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v378 dropping h_v380 h_v381 he_v382 hinv268 e_v382 s268 v380 v381
          step as ⟨e_v383, he_v383⟩
          store_step with CtorSpec.eo_extract.construct s269 e_v383 (by rw [he_v383]; rfl) h_v378 h_v382 hinv269 h64 as ⟨v383, s270, hinv270, h_v383⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 dropping h_v378 h_v382 he_v383 hinv269 e_v383 s269 v378 v382
          step as ⟨e_v384, he_v384⟩
          store_step with CtorSpec.eo_bvmul.construct s270 e_v384 (by rw [he_v384]; exact empty_args) hinv270 h64 as ⟨v384, s271, hinv271, h_v384⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 dropping he_v384 hinv270 e_v384 s270
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s271 1#u32 (1) (by scalar_tac) hinv271 h64 as ⟨v385, s272, hinv272, h_v385⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v384 dropping hinv271 s271
          step as ⟨e_v386, he_v386⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s272 e_v386 (by rw [he_v386]; rfl) h_v385 hinv272 h64 as ⟨v386, s273, hinv273, h_v386⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v384 dropping h_v385 he_v386 hinv272 e_v386 s272 v385
          store_step with Store.apply_rep s273 v386 v12 _ _ hinv273 h64 h_v386 h_v12 (by ns_tac) (by ns_tac) as ⟨v387, s274, hinv274, h_v387⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v384 dropping h_v386 hinv273 s273 v386
          store_step with Store.apply_rep s274 v384 v387 _ _ hinv274 h64 h_v384 h_v387 (by ns_tac) (by ns_tac) as ⟨v388, s275, hinv275, h_v388⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 dropping h_v384 h_v387 hinv274 s274 v384 v387
          step as ⟨e_v389, he_v389⟩
          store_step with CtorSpec.eo_bvmul.construct s275 e_v389 (by rw [he_v389]; exact empty_args) hinv275 h64 as ⟨v389, s276, hinv276, h_v389⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 dropping he_v389 hinv275 e_v389 s275
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s276 1#u32 (1) (by scalar_tac) hinv276 h64 as ⟨v390, s277, hinv277, h_v390⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v389 dropping hinv276 s276
          step as ⟨e_v391, he_v391⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s277 e_v391 (by rw [he_v391]; rfl) h_v390 hinv277 h64 as ⟨v391, s278, hinv278, h_v391⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v389 dropping h_v390 he_v391 hinv277 e_v391 s277 v390
          store_step with Store.apply_rep s278 v391 v9 _ _ hinv278 h64 h_v391 h_v9 (by ns_tac) (by ns_tac) as ⟨v392, s279, hinv279, h_v392⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v389 dropping h_v391 hinv278 s278 v391
          store_step with Store.apply_rep s279 v389 v392 _ _ hinv279 h64 h_v389 h_v392 (by ns_tac) (by ns_tac) as ⟨v393, s280, hinv280, h_v393⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 dropping h_v389 h_v392 hinv279 s279 v389 v392
          step as ⟨e_v394, he_v394⟩
          store_step with CtorSpec.eo_bvmul.construct s280 e_v394 (by rw [he_v394]; exact empty_args) hinv280 h64 as ⟨v394, s281, hinv281, h_v394⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v393 dropping he_v394 hinv280 e_v394 s280
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s281 1#u32 (1) (by scalar_tac) hinv281 h64 as ⟨v395, s282, hinv282, h_v395⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v393 h_v394 dropping hinv281 s281
          step as ⟨e_v396, he_v396⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s282 e_v396 (by rw [he_v396]; rfl) h_v395 hinv282 h64 as ⟨v396, s283, hinv283, h_v396⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v393 h_v394 dropping h_v395 he_v396 hinv282 e_v396 s282 v395
          store_step with Store.apply_rep s283 v396 v12 _ _ hinv283 h64 h_v396 h_v12 (by ns_tac) (by ns_tac) as ⟨v397, s284, hinv284, h_v397⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v393 h_v394 dropping h_v396 hinv283 s283 v396
          store_step with ih.eo__24eo_5ftypeof s284 v397 _ hinv284 h64 (hG.rem hrem) h_v397 as ⟨v398, s285, hinv285, h_v398⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v393 h_v394 dropping h_v397 hinv284 s284 v397
          store_step with ih.eo__24eo_5fnil s285 v394 v398 _ _ hinv285 h64 (hG.rem hrem) h_v394 h_v398 as ⟨v399, s286, hinv286, h_v399⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 h_v393 dropping h_v394 h_v398 hinv285 s285 v394 v398
          store_step with Store.apply_mk_rep s286 v393 v399 _ _ hinv286 h64 h_v393 h_v399 as ⟨v400, s287, hinv287, h_v400⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 h_v388 dropping h_v393 h_v399 hinv286 s286 v393 v399
          store_step with Store.apply_mk_rep s287 v388 v400 _ _ hinv287 h64 h_v388 h_v400 as ⟨v401, s288, hinv288, h_v401⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 h_v383 dropping h_v388 h_v400 hinv287 s287 v388 v400
          store_step with Store.apply_mk_rep s288 v383 v401 _ _ hinv288 h64 h_v383 h_v401 as ⟨v402, s289, hinv289, h_v402⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v374 dropping h_v383 h_v401 hinv288 s288 v383 v401
          store_step with Store.apply_mk_rep s289 v374 v402 _ _ hinv289 h64 h_v374 h_v402 as ⟨v403, s290, hinv290, h_v403⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 dropping h_v374 h_v402 hinv289 s289 v374 v402
          step as ⟨e_v404, he_v404⟩
          store_step with CtorSpec.eo_bvxor.construct s290 e_v404 (by rw [he_v404]; exact empty_args) hinv290 h64 as ⟨v404, s291, hinv291, h_v404⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 dropping he_v404 hinv290 e_v404 s290
          store_step with ih.eo__24eo_5ftypeof s291 v12 _ hinv291 h64 (hG.rem hrem) h_v12 as ⟨v405, s292, hinv292, h_v405⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 dropping hinv291 s291
          store_step with ih.eo__24bv_5fbitwidth s292 v405 _ hinv292 h64 (hG.rem hrem) h_v405 as ⟨v406, s293, hinv293, h_v406⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 dropping h_v405 hinv292 s292 v405
          store_step with ih.eo__24eo_5ftypeof s293 v12 _ hinv293 h64 (hG.rem hrem) h_v12 as ⟨v407, s294, hinv294, h_v407⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v406 dropping hinv293 s293
          store_step with ih.eo__24bv_5fbitwidth s294 v407 _ hinv294 h64 (hG.rem hrem) h_v407 as ⟨v408, s295, hinv295, h_v408⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v406 dropping h_v407 hinv294 s294 v407
          step as ⟨e_v409, he_v409⟩
          store_step with CtorSpec.eo_extract.construct s295 e_v409 (by rw [he_v409]; rfl) h_v406 h_v408 hinv295 h64 as ⟨v409, s296, hinv296, h_v409⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 dropping h_v406 h_v408 he_v409 hinv295 e_v409 s295 v406 v408
          step as ⟨e_v410, he_v410⟩
          store_step with CtorSpec.eo_bvmul.construct s296 e_v410 (by rw [he_v410]; exact empty_args) hinv296 h64 as ⟨v410, s297, hinv297, h_v410⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 dropping he_v410 hinv296 e_v410 s296
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s297 1#u32 (1) (by scalar_tac) hinv297 h64 as ⟨v411, s298, hinv298, h_v411⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v410 dropping hinv297 s297
          step as ⟨e_v412, he_v412⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s298 e_v412 (by rw [he_v412]; rfl) h_v411 hinv298 h64 as ⟨v412, s299, hinv299, h_v412⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v410 dropping h_v411 he_v412 hinv298 e_v412 s298 v411
          store_step with Store.apply_rep s299 v412 v12 _ _ hinv299 h64 h_v412 h_v12 (by ns_tac) (by ns_tac) as ⟨v413, s300, hinv300, h_v413⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v410 dropping h_v412 hinv299 s299 v412
          store_step with Store.apply_rep s300 v410 v413 _ _ hinv300 h64 h_v410 h_v413 (by ns_tac) (by ns_tac) as ⟨v414, s301, hinv301, h_v414⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 dropping h_v410 h_v413 hinv300 s300 v410 v413
          step as ⟨e_v415, he_v415⟩
          store_step with CtorSpec.eo_bvmul.construct s301 e_v415 (by rw [he_v415]; exact empty_args) hinv301 h64 as ⟨v415, s302, hinv302, h_v415⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 dropping he_v415 hinv301 e_v415 s301
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s302 1#u32 (1) (by scalar_tac) hinv302 h64 as ⟨v416, s303, hinv303, h_v416⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v415 dropping hinv302 s302
          step as ⟨e_v417, he_v417⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s303 e_v417 (by rw [he_v417]; rfl) h_v416 hinv303 h64 as ⟨v417, s304, hinv304, h_v417⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v415 dropping h_v416 he_v417 hinv303 e_v417 s303 v416
          store_step with Store.apply_rep s304 v417 v9 _ _ hinv304 h64 h_v417 h_v9 (by ns_tac) (by ns_tac) as ⟨v418, s305, hinv305, h_v418⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v415 dropping h_v417 hinv304 s304 v417
          store_step with Store.apply_rep s305 v415 v418 _ _ hinv305 h64 h_v415 h_v418 (by ns_tac) (by ns_tac) as ⟨v419, s306, hinv306, h_v419⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 dropping h_v415 h_v418 hinv305 s305 v415 v418
          step as ⟨e_v420, he_v420⟩
          store_step with CtorSpec.eo_bvmul.construct s306 e_v420 (by rw [he_v420]; exact empty_args) hinv306 h64 as ⟨v420, s307, hinv307, h_v420⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v419 dropping he_v420 hinv306 e_v420 s306
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s307 1#u32 (1) (by scalar_tac) hinv307 h64 as ⟨v421, s308, hinv308, h_v421⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v419 h_v420 dropping hinv307 s307
          step as ⟨e_v422, he_v422⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s308 e_v422 (by rw [he_v422]; rfl) h_v421 hinv308 h64 as ⟨v422, s309, hinv309, h_v422⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v419 h_v420 dropping h_v421 he_v422 hinv308 e_v422 s308 v421
          store_step with Store.apply_rep s309 v422 v12 _ _ hinv309 h64 h_v422 h_v12 (by ns_tac) (by ns_tac) as ⟨v423, s310, hinv310, h_v423⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v419 h_v420 dropping h_v422 hinv309 s309 v422
          store_step with ih.eo__24eo_5ftypeof s310 v423 _ hinv310 h64 (hG.rem hrem) h_v423 as ⟨v424, s311, hinv311, h_v424⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v419 h_v420 dropping h_v423 hinv310 s310 v423
          store_step with ih.eo__24eo_5fnil s311 v420 v424 _ _ hinv311 h64 (hG.rem hrem) h_v420 h_v424 as ⟨v425, s312, hinv312, h_v425⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 h_v419 dropping h_v420 h_v424 hinv311 s311 v420 v424
          store_step with Store.apply_mk_rep s312 v419 v425 _ _ hinv312 h64 h_v419 h_v425 as ⟨v426, s313, hinv313, h_v426⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 h_v414 dropping h_v419 h_v425 hinv312 s312 v419 v425
          store_step with Store.apply_mk_rep s313 v414 v426 _ _ hinv313 h64 h_v414 h_v426 as ⟨v427, s314, hinv314, h_v427⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 h_v409 dropping h_v414 h_v426 hinv313 s313 v414 v426
          store_step with Store.apply_mk_rep s314 v409 v427 _ _ hinv314 h64 h_v409 h_v427 as ⟨v428, s315, hinv315, h_v428⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 dropping h_v409 h_v427 hinv314 s314 v409 v427
          store_step with ih.eo__24eo_5ftypeof s315 v428 _ hinv315 h64 (hG.rem hrem) h_v428 as ⟨v429, s316, hinv316, h_v429⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 h_v404 dropping h_v428 hinv315 s315 v428
          store_step with ih.eo__24eo_5fnil s316 v404 v429 _ _ hinv316 h64 (hG.rem hrem) h_v404 h_v429 as ⟨v430, s317, hinv317, h_v430⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 h_v403 dropping h_v404 h_v429 hinv316 s316 v404 v429
          store_step with Store.apply_mk_rep s317 v403 v430 _ _ hinv317 h64 h_v403 h_v430 as ⟨v431, s318, hinv318, h_v431⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 h_v373 dropping h_v403 h_v430 hinv317 s317 v403 v430
          store_step with Store.apply_mk_rep s318 v373 v431 _ _ hinv318 h64 h_v373 h_v431 as ⟨v432, s319, hinv319, h_v432⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v347 dropping h_v373 h_v431 hinv318 s318 v373 v431
          store_step with Store.apply_mk_rep s319 v347 v432 _ _ hinv319 h64 h_v347 h_v432 as ⟨v433, s320, hinv320, h_v433⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 dropping h_v347 h_v432 hinv319 s319 v347 v432
          step as ⟨e_v434, he_v434⟩
          store_step with CtorSpec.eo_bvor.construct s320 e_v434 (by rw [he_v434]; exact empty_args) hinv320 h64 as ⟨v434, s321, hinv321, h_v434⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 dropping he_v434 hinv320 e_v434 s320
          step as ⟨e_v435, he_v435⟩
          store_step with CtorSpec.eo_bvxor.construct s321 e_v435 (by rw [he_v435]; exact empty_args) hinv321 h64 as ⟨v435, s322, hinv322, h_v435⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 dropping he_v435 hinv321 e_v435 s321
          store_step with Store.apply_rep s322 v435 v12 _ _ hinv322 h64 h_v435 h_v12 (by ns_tac) (by ns_tac) as ⟨v436, s323, hinv323, h_v436⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 dropping h_v435 hinv322 s322 v435
          step as ⟨e_v437, he_v437⟩
          store_step with CtorSpec.eo_bvxor.construct s323 e_v437 (by rw [he_v437]; exact empty_args) hinv323 h64 as ⟨v437, s324, hinv324, h_v437⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 dropping he_v437 hinv323 e_v437 s323
          store_step with ih.eo__24eo_5ftypeof s324 v12 _ hinv324 h64 (hG.rem hrem) h_v12 as ⟨v438, s325, hinv325, h_v438⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 dropping hinv324 s324
          store_step with ih.eo__24bv_5fbitwidth s325 v438 _ hinv325 h64 (hG.rem hrem) h_v438 as ⟨v439, s326, hinv326, h_v439⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 dropping h_v438 hinv325 s325 v438
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s326 1#u32 (-1) (by scalar_tac) hinv326 h64 as ⟨v440, s327, hinv327, h_v440⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v439 dropping hinv326 s326
          step as ⟨e_v441, he_v441⟩
          store_step with Store.builtin_spec_add s327 e_v441 (by rw [he_v441]; rfl) h_v439 h_v440 hinv327 h64 as ⟨v441, s328, hinv328, h_v441⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 dropping h_v439 h_v440 he_v441 hinv327 e_v441 s327 v439 v440
          step as ⟨e_v442, he_v442⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s328 e_v442 (by rw [he_v442]; rfl) h_v441 hinv328 h64 as ⟨v442, s329, hinv329, h_v442⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 dropping h_v441 he_v442 hinv328 e_v442 s328 v441
          store_step with ih.eo__24eo_5ftypeof s329 v12 _ hinv329 h64 (hG.rem hrem) h_v12 as ⟨v443, s330, hinv330, h_v443⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 dropping hinv329 s329
          store_step with ih.eo__24bv_5fbitwidth s330 v443 _ hinv330 h64 (hG.rem hrem) h_v443 as ⟨v444, s331, hinv331, h_v444⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 dropping h_v443 hinv330 s330 v443
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s331 1#u32 (-1) (by scalar_tac) hinv331 h64 as ⟨v445, s332, hinv332, h_v445⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 h_v444 dropping hinv331 s331
          step as ⟨e_v446, he_v446⟩
          store_step with Store.builtin_spec_add s332 e_v446 (by rw [he_v446]; rfl) h_v444 h_v445 hinv332 h64 as ⟨v446, s333, hinv333, h_v446⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 dropping h_v444 h_v445 he_v446 hinv332 e_v446 s332 v444 v445
          store_step with ih.eo__24eo_5ftypeof s333 v12 _ hinv333 h64 (hG.rem hrem) h_v12 as ⟨v447, s334, hinv334, h_v447⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 h_v446 dropping hinv333 s333
          store_step with ih.eo__24bv_5fbitwidth s334 v447 _ hinv334 h64 (hG.rem hrem) h_v447 as ⟨v448, s335, hinv335, h_v448⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 h_v446 dropping h_v447 hinv334 s334 v447
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s335 1#u32 (-1) (by scalar_tac) hinv335 h64 as ⟨v449, s336, hinv336, h_v449⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 h_v446 h_v448 dropping hinv335 s335
          step as ⟨e_v450, he_v450⟩
          store_step with Store.builtin_spec_add s336 e_v450 (by rw [he_v450]; rfl) h_v448 h_v449 hinv336 h64 as ⟨v450, s337, hinv337, h_v450⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 h_v446 dropping h_v448 h_v449 he_v450 hinv336 e_v450 s336 v448 v449
          step as ⟨e_v451, he_v451⟩
          store_step with CtorSpec.eo_extract.construct s337 e_v451 (by rw [he_v451]; rfl) h_v446 h_v450 hinv337 h64 as ⟨v451, s338, hinv338, h_v451⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 dropping h_v446 h_v450 he_v451 hinv337 e_v451 s337 v446 v450
          store_step with Store.apply_mk_rep s338 v451 v12 _ _ hinv338 h64 h_v451 h_v12 as ⟨v452, s339, hinv339, h_v452⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 h_v442 dropping h_v451 hinv338 s338 v451
          store_step with Store.apply_mk_rep s339 v442 v452 _ _ hinv339 h64 h_v442 h_v452 as ⟨v453, s340, hinv340, h_v453⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v437 dropping h_v442 h_v452 hinv339 s339 v442 v452
          store_step with Store.apply_mk_rep s340 v437 v453 _ _ hinv340 h64 h_v437 h_v453 as ⟨v454, s341, hinv341, h_v454⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 dropping h_v437 h_v453 hinv340 s340 v437 v453
          step as ⟨e_v455, he_v455⟩
          store_step with CtorSpec.eo_bvxor.construct s341 e_v455 (by rw [he_v455]; exact empty_args) hinv341 h64 as ⟨v455, s342, hinv342, h_v455⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v454 dropping he_v455 hinv341 e_v455 s341
          store_step with ih.eo__24eo_5ftypeof s342 v12 _ hinv342 h64 (hG.rem hrem) h_v12 as ⟨v456, s343, hinv343, h_v456⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v454 h_v455 dropping hinv342 s342
          store_step with ih.eo__24eo_5fnil s343 v455 v456 _ _ hinv343 h64 (hG.rem hrem) h_v455 h_v456 as ⟨v457, s344, hinv344, h_v457⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 h_v454 dropping h_v455 h_v456 hinv343 s343 v455 v456
          store_step with Store.apply_mk_rep s344 v454 v457 _ _ hinv344 h64 h_v454 h_v457 as ⟨v458, s345, hinv345, h_v458⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v436 dropping h_v454 h_v457 hinv344 s344 v454 v457
          store_step with Store.apply_mk_rep s345 v436 v458 _ _ hinv345 h64 h_v436 h_v458 as ⟨v459, s346, hinv346, h_v459⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 dropping h_v436 h_v458 hinv345 s345 v436 v458
          step as ⟨e_v460, he_v460⟩
          store_step with CtorSpec.eo_bvxor.construct s346 e_v460 (by rw [he_v460]; exact empty_args) hinv346 h64 as ⟨v460, s347, hinv347, h_v460⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 dropping he_v460 hinv346 e_v460 s346
          store_step with Store.apply_rep s347 v460 v9 _ _ hinv347 h64 h_v460 h_v9 (by ns_tac) (by ns_tac) as ⟨v461, s348, hinv348, h_v461⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 dropping h_v460 hinv347 s347 v460
          step as ⟨e_v462, he_v462⟩
          store_step with CtorSpec.eo_bvxor.construct s348 e_v462 (by rw [he_v462]; exact empty_args) hinv348 h64 as ⟨v462, s349, hinv349, h_v462⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 dropping he_v462 hinv348 e_v462 s348
          store_step with ih.eo__24eo_5ftypeof s349 v12 _ hinv349 h64 (hG.rem hrem) h_v12 as ⟨v463, s350, hinv350, h_v463⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 dropping hinv349 s349
          store_step with ih.eo__24bv_5fbitwidth s350 v463 _ hinv350 h64 (hG.rem hrem) h_v463 as ⟨v464, s351, hinv351, h_v464⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 dropping h_v463 hinv350 s350 v463
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s351 1#u32 (-1) (by scalar_tac) hinv351 h64 as ⟨v465, s352, hinv352, h_v465⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v464 dropping hinv351 s351
          step as ⟨e_v466, he_v466⟩
          store_step with Store.builtin_spec_add s352 e_v466 (by rw [he_v466]; rfl) h_v464 h_v465 hinv352 h64 as ⟨v466, s353, hinv353, h_v466⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 dropping h_v464 h_v465 he_v466 hinv352 e_v466 s352 v464 v465
          step as ⟨e_v467, he_v467⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s353 e_v467 (by rw [he_v467]; rfl) h_v466 hinv353 h64 as ⟨v467, s354, hinv354, h_v467⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 dropping h_v466 he_v467 hinv353 e_v467 s353 v466
          store_step with ih.eo__24eo_5ftypeof s354 v12 _ hinv354 h64 (hG.rem hrem) h_v12 as ⟨v468, s355, hinv355, h_v468⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 dropping hinv354 s354
          store_step with ih.eo__24bv_5fbitwidth s355 v468 _ hinv355 h64 (hG.rem hrem) h_v468 as ⟨v469, s356, hinv356, h_v469⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 dropping h_v468 hinv355 s355 v468
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s356 1#u32 (-1) (by scalar_tac) hinv356 h64 as ⟨v470, s357, hinv357, h_v470⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 h_v469 dropping hinv356 s356
          step as ⟨e_v471, he_v471⟩
          store_step with Store.builtin_spec_add s357 e_v471 (by rw [he_v471]; rfl) h_v469 h_v470 hinv357 h64 as ⟨v471, s358, hinv358, h_v471⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 dropping h_v469 h_v470 he_v471 hinv357 e_v471 s357 v469 v470
          store_step with ih.eo__24eo_5ftypeof s358 v12 _ hinv358 h64 (hG.rem hrem) h_v12 as ⟨v472, s359, hinv359, h_v472⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 h_v471 dropping hinv358 s358
          store_step with ih.eo__24bv_5fbitwidth s359 v472 _ hinv359 h64 (hG.rem hrem) h_v472 as ⟨v473, s360, hinv360, h_v473⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 h_v471 dropping h_v472 hinv359 s359 v472
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s360 1#u32 (-1) (by scalar_tac) hinv360 h64 as ⟨v474, s361, hinv361, h_v474⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 h_v471 h_v473 dropping hinv360 s360
          step as ⟨e_v475, he_v475⟩
          store_step with Store.builtin_spec_add s361 e_v475 (by rw [he_v475]; rfl) h_v473 h_v474 hinv361 h64 as ⟨v475, s362, hinv362, h_v475⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 h_v471 dropping h_v473 h_v474 he_v475 hinv361 e_v475 s361 v473 v474
          step as ⟨e_v476, he_v476⟩
          store_step with CtorSpec.eo_extract.construct s362 e_v476 (by rw [he_v476]; rfl) h_v471 h_v475 hinv362 h64 as ⟨v476, s363, hinv363, h_v476⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 dropping h_v471 h_v475 he_v476 hinv362 e_v476 s362 v471 v475
          store_step with Store.apply_mk_rep s363 v476 v9 _ _ hinv363 h64 h_v476 h_v9 as ⟨v477, s364, hinv364, h_v477⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 h_v467 dropping h_v476 hinv363 s363 v476
          store_step with Store.apply_mk_rep s364 v467 v477 _ _ hinv364 h64 h_v467 h_v477 as ⟨v478, s365, hinv365, h_v478⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v462 dropping h_v467 h_v477 hinv364 s364 v467 v477
          store_step with Store.apply_mk_rep s365 v462 v478 _ _ hinv365 h64 h_v462 h_v478 as ⟨v479, s366, hinv366, h_v479⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 dropping h_v462 h_v478 hinv365 s365 v462 v478
          step as ⟨e_v480, he_v480⟩
          store_step with CtorSpec.eo_bvxor.construct s366 e_v480 (by rw [he_v480]; exact empty_args) hinv366 h64 as ⟨v480, s367, hinv367, h_v480⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v479 dropping he_v480 hinv366 e_v480 s366
          store_step with ih.eo__24eo_5ftypeof s367 v9 _ hinv367 h64 (hG.rem hrem) h_v9 as ⟨v481, s368, hinv368, h_v481⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v479 h_v480 dropping hinv367 s367
          store_step with ih.eo__24eo_5fnil s368 v480 v481 _ _ hinv368 h64 (hG.rem hrem) h_v480 h_v481 as ⟨v482, s369, hinv369, h_v482⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 h_v479 dropping h_v480 h_v481 hinv368 s368 v480 v481
          store_step with Store.apply_mk_rep s369 v479 v482 _ _ hinv369 h64 h_v479 h_v482 as ⟨v483, s370, hinv370, h_v483⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v461 dropping h_v479 h_v482 hinv369 s369 v479 v482
          store_step with Store.apply_mk_rep s370 v461 v483 _ _ hinv370 h64 h_v461 h_v483 as ⟨v484, s371, hinv371, h_v484⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 dropping h_v461 h_v483 hinv370 s370 v461 v483
          store_step with ih.eo__24eo_5ftypeof s371 v12 _ hinv371 h64 (hG.rem hrem) h_v12 as ⟨v485, s372, hinv372, h_v485⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 dropping hinv371 s371
          store_step with ih.eo__24bv_5fbitwidth s372 v485 _ hinv372 h64 (hG.rem hrem) h_v485 as ⟨v486, s373, hinv373, h_v486⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 dropping h_v485 hinv372 s372 v485
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s373 2#u32 (-2) (by scalar_tac) hinv373 h64 as ⟨v487, s374, hinv374, h_v487⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v486 dropping hinv373 s373
          step as ⟨e_v488, he_v488⟩
          store_step with Store.builtin_spec_add s374 e_v488 (by rw [he_v488]; rfl) h_v486 h_v487 hinv374 h64 as ⟨v488, s375, hinv375, h_v488⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 dropping h_v486 h_v487 he_v488 hinv374 e_v488 s374 v486 v487
          store_step with ih.eo__24eo_5ftypeof s375 v12 _ hinv375 h64 (hG.rem hrem) h_v12 as ⟨v489, s376, hinv376, h_v489⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v488 dropping hinv375 s375
          store_step with ih.eo__24bv_5fbitwidth s376 v489 _ hinv376 h64 (hG.rem hrem) h_v489 as ⟨v490, s377, hinv377, h_v490⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v488 dropping h_v489 hinv376 s376 v489
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s377 2#u32 (-2) (by scalar_tac) hinv377 h64 as ⟨v491, s378, hinv378, h_v491⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v488 h_v490 dropping hinv377 s377
          step as ⟨e_v492, he_v492⟩
          store_step with Store.builtin_spec_add s378 e_v492 (by rw [he_v492]; rfl) h_v490 h_v491 hinv378 h64 as ⟨v492, s379, hinv379, h_v492⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v488 dropping h_v490 h_v491 he_v492 hinv378 e_v492 s378 v490 v491
          step as ⟨e_v493, he_v493⟩
          store_step with CtorSpec.eo_extract.construct s379 e_v493 (by rw [he_v493]; rfl) h_v488 h_v492 hinv379 h64 as ⟨v493, s380, hinv380, h_v493⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 dropping h_v488 h_v492 he_v493 hinv379 e_v493 s379 v488 v492
          step as ⟨e_v494, he_v494⟩
          store_step with CtorSpec.eo_bvxor.construct s380 e_v494 (by rw [he_v494]; exact empty_args) hinv380 h64 as ⟨v494, s381, hinv381, h_v494⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 dropping he_v494 hinv380 e_v494 s380
          store_step with Store.apply_rep s381 v494 v12 _ _ hinv381 h64 h_v494 h_v12 (by ns_tac) (by ns_tac) as ⟨v495, s382, hinv382, h_v495⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 dropping h_v494 hinv381 s381 v494
          step as ⟨e_v496, he_v496⟩
          store_step with CtorSpec.eo_bvxor.construct s382 e_v496 (by rw [he_v496]; exact empty_args) hinv382 h64 as ⟨v496, s383, hinv383, h_v496⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 dropping he_v496 hinv382 e_v496 s382
          store_step with ih.eo__24eo_5ftypeof s383 v12 _ hinv383 h64 (hG.rem hrem) h_v12 as ⟨v497, s384, hinv384, h_v497⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 dropping hinv383 s383
          store_step with ih.eo__24bv_5fbitwidth s384 v497 _ hinv384 h64 (hG.rem hrem) h_v497 as ⟨v498, s385, hinv385, h_v498⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 dropping h_v497 hinv384 s384 v497
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s385 1#u32 (-1) (by scalar_tac) hinv385 h64 as ⟨v499, s386, hinv386, h_v499⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v498 dropping hinv385 s385
          step as ⟨e_v500, he_v500⟩
          store_step with Store.builtin_spec_add s386 e_v500 (by rw [he_v500]; rfl) h_v498 h_v499 hinv386 h64 as ⟨v500, s387, hinv387, h_v500⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 dropping h_v498 h_v499 he_v500 hinv386 e_v500 s386 v498 v499
          step as ⟨e_v501, he_v501⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s387 e_v501 (by rw [he_v501]; rfl) h_v500 hinv387 h64 as ⟨v501, s388, hinv388, h_v501⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 dropping h_v500 he_v501 hinv387 e_v501 s387 v500
          store_step with ih.eo__24eo_5ftypeof s388 v12 _ hinv388 h64 (hG.rem hrem) h_v12 as ⟨v502, s389, hinv389, h_v502⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 dropping hinv388 s388
          store_step with ih.eo__24bv_5fbitwidth s389 v502 _ hinv389 h64 (hG.rem hrem) h_v502 as ⟨v503, s390, hinv390, h_v503⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 dropping h_v502 hinv389 s389 v502
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s390 1#u32 (-1) (by scalar_tac) hinv390 h64 as ⟨v504, s391, hinv391, h_v504⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 h_v503 dropping hinv390 s390
          step as ⟨e_v505, he_v505⟩
          store_step with Store.builtin_spec_add s391 e_v505 (by rw [he_v505]; rfl) h_v503 h_v504 hinv391 h64 as ⟨v505, s392, hinv392, h_v505⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 dropping h_v503 h_v504 he_v505 hinv391 e_v505 s391 v503 v504
          store_step with ih.eo__24eo_5ftypeof s392 v12 _ hinv392 h64 (hG.rem hrem) h_v12 as ⟨v506, s393, hinv393, h_v506⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 h_v505 dropping hinv392 s392
          store_step with ih.eo__24bv_5fbitwidth s393 v506 _ hinv393 h64 (hG.rem hrem) h_v506 as ⟨v507, s394, hinv394, h_v507⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 h_v505 dropping h_v506 hinv393 s393 v506
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s394 1#u32 (-1) (by scalar_tac) hinv394 h64 as ⟨v508, s395, hinv395, h_v508⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 h_v505 h_v507 dropping hinv394 s394
          step as ⟨e_v509, he_v509⟩
          store_step with Store.builtin_spec_add s395 e_v509 (by rw [he_v509]; rfl) h_v507 h_v508 hinv395 h64 as ⟨v509, s396, hinv396, h_v509⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 h_v505 dropping h_v507 h_v508 he_v509 hinv395 e_v509 s395 v507 v508
          step as ⟨e_v510, he_v510⟩
          store_step with CtorSpec.eo_extract.construct s396 e_v510 (by rw [he_v510]; rfl) h_v505 h_v509 hinv396 h64 as ⟨v510, s397, hinv397, h_v510⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 dropping h_v505 h_v509 he_v510 hinv396 e_v510 s396 v505 v509
          store_step with Store.apply_mk_rep s397 v510 v12 _ _ hinv397 h64 h_v510 h_v12 as ⟨v511, s398, hinv398, h_v511⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 h_v501 dropping h_v510 hinv397 s397 v510
          store_step with Store.apply_mk_rep s398 v501 v511 _ _ hinv398 h64 h_v501 h_v511 as ⟨v512, s399, hinv399, h_v512⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v496 dropping h_v501 h_v511 hinv398 s398 v501 v511
          store_step with Store.apply_mk_rep s399 v496 v512 _ _ hinv399 h64 h_v496 h_v512 as ⟨v513, s400, hinv400, h_v513⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 dropping h_v496 h_v512 hinv399 s399 v496 v512
          step as ⟨e_v514, he_v514⟩
          store_step with CtorSpec.eo_bvxor.construct s400 e_v514 (by rw [he_v514]; exact empty_args) hinv400 h64 as ⟨v514, s401, hinv401, h_v514⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v513 dropping he_v514 hinv400 e_v514 s400
          store_step with ih.eo__24eo_5ftypeof s401 v12 _ hinv401 h64 (hG.rem hrem) h_v12 as ⟨v515, s402, hinv402, h_v515⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v513 h_v514 dropping hinv401 s401
          store_step with ih.eo__24eo_5fnil s402 v514 v515 _ _ hinv402 h64 (hG.rem hrem) h_v514 h_v515 as ⟨v516, s403, hinv403, h_v516⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 h_v513 dropping h_v514 h_v515 hinv402 s402 v514 v515
          store_step with Store.apply_mk_rep s403 v513 v516 _ _ hinv403 h64 h_v513 h_v516 as ⟨v517, s404, hinv404, h_v517⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 h_v495 dropping h_v513 h_v516 hinv403 s403 v513 v516
          store_step with Store.apply_mk_rep s404 v495 v517 _ _ hinv404 h64 h_v495 h_v517 as ⟨v518, s405, hinv405, h_v518⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v493 dropping h_v495 h_v517 hinv404 s404 v495 v517
          store_step with Store.apply_mk_rep s405 v493 v518 _ _ hinv405 h64 h_v493 h_v518 as ⟨v519, s406, hinv406, h_v519⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 dropping h_v493 h_v518 hinv405 s405 v493 v518
          step as ⟨e_v520, he_v520⟩
          store_step with CtorSpec.eo_bvand.construct s406 e_v520 (by rw [he_v520]; exact empty_args) hinv406 h64 as ⟨v520, s407, hinv407, h_v520⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 dropping he_v520 hinv406 e_v520 s406
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s407 1#u32 (1) (by scalar_tac) hinv407 h64 as ⟨v521, s408, hinv408, h_v521⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 dropping hinv407 s407
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s408 1#u32 (1) (by scalar_tac) hinv408 h64 as ⟨v522, s409, hinv409, h_v522⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v521 dropping hinv408 s408
          step as ⟨e_v523, he_v523⟩
          store_step with CtorSpec.eo_extract.construct s409 e_v523 (by rw [he_v523]; rfl) h_v521 h_v522 hinv409 h64 as ⟨v523, s410, hinv410, h_v523⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 dropping h_v521 h_v522 he_v523 hinv409 e_v523 s409 v521 v522
          step as ⟨e_v524, he_v524⟩
          store_step with CtorSpec.eo_bvxor.construct s410 e_v524 (by rw [he_v524]; exact empty_args) hinv410 h64 as ⟨v524, s411, hinv411, h_v524⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 dropping he_v524 hinv410 e_v524 s410
          store_step with Store.apply_rep s411 v524 v9 _ _ hinv411 h64 h_v524 h_v9 (by ns_tac) (by ns_tac) as ⟨v525, s412, hinv412, h_v525⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 dropping h_v524 hinv411 s411 v524
          step as ⟨e_v526, he_v526⟩
          store_step with CtorSpec.eo_bvxor.construct s412 e_v526 (by rw [he_v526]; exact empty_args) hinv412 h64 as ⟨v526, s413, hinv413, h_v526⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 dropping he_v526 hinv412 e_v526 s412
          store_step with ih.eo__24eo_5ftypeof s413 v12 _ hinv413 h64 (hG.rem hrem) h_v12 as ⟨v527, s414, hinv414, h_v527⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 dropping hinv413 s413
          store_step with ih.eo__24bv_5fbitwidth s414 v527 _ hinv414 h64 (hG.rem hrem) h_v527 as ⟨v528, s415, hinv415, h_v528⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 dropping h_v527 hinv414 s414 v527
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s415 1#u32 (-1) (by scalar_tac) hinv415 h64 as ⟨v529, s416, hinv416, h_v529⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v528 dropping hinv415 s415
          step as ⟨e_v530, he_v530⟩
          store_step with Store.builtin_spec_add s416 e_v530 (by rw [he_v530]; rfl) h_v528 h_v529 hinv416 h64 as ⟨v530, s417, hinv417, h_v530⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 dropping h_v528 h_v529 he_v530 hinv416 e_v530 s416 v528 v529
          step as ⟨e_v531, he_v531⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s417 e_v531 (by rw [he_v531]; rfl) h_v530 hinv417 h64 as ⟨v531, s418, hinv418, h_v531⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 dropping h_v530 he_v531 hinv417 e_v531 s417 v530
          store_step with ih.eo__24eo_5ftypeof s418 v12 _ hinv418 h64 (hG.rem hrem) h_v12 as ⟨v532, s419, hinv419, h_v532⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 dropping hinv418 s418
          store_step with ih.eo__24bv_5fbitwidth s419 v532 _ hinv419 h64 (hG.rem hrem) h_v532 as ⟨v533, s420, hinv420, h_v533⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 dropping h_v532 hinv419 s419 v532
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s420 1#u32 (-1) (by scalar_tac) hinv420 h64 as ⟨v534, s421, hinv421, h_v534⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 h_v533 dropping hinv420 s420
          step as ⟨e_v535, he_v535⟩
          store_step with Store.builtin_spec_add s421 e_v535 (by rw [he_v535]; rfl) h_v533 h_v534 hinv421 h64 as ⟨v535, s422, hinv422, h_v535⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 dropping h_v533 h_v534 he_v535 hinv421 e_v535 s421 v533 v534
          store_step with ih.eo__24eo_5ftypeof s422 v12 _ hinv422 h64 (hG.rem hrem) h_v12 as ⟨v536, s423, hinv423, h_v536⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 h_v535 dropping hinv422 s422
          store_step with ih.eo__24bv_5fbitwidth s423 v536 _ hinv423 h64 (hG.rem hrem) h_v536 as ⟨v537, s424, hinv424, h_v537⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 h_v535 dropping h_v536 hinv423 s423 v536
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s424 1#u32 (-1) (by scalar_tac) hinv424 h64 as ⟨v538, s425, hinv425, h_v538⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 h_v535 h_v537 dropping hinv424 s424
          step as ⟨e_v539, he_v539⟩
          store_step with Store.builtin_spec_add s425 e_v539 (by rw [he_v539]; rfl) h_v537 h_v538 hinv425 h64 as ⟨v539, s426, hinv426, h_v539⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 h_v535 dropping h_v537 h_v538 he_v539 hinv425 e_v539 s425 v537 v538
          step as ⟨e_v540, he_v540⟩
          store_step with CtorSpec.eo_extract.construct s426 e_v540 (by rw [he_v540]; rfl) h_v535 h_v539 hinv426 h64 as ⟨v540, s427, hinv427, h_v540⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 dropping h_v535 h_v539 he_v540 hinv426 e_v540 s426 v535 v539
          store_step with Store.apply_mk_rep s427 v540 v9 _ _ hinv427 h64 h_v540 h_v9 as ⟨v541, s428, hinv428, h_v541⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 h_v531 dropping h_v540 hinv427 s427 v540
          store_step with Store.apply_mk_rep s428 v531 v541 _ _ hinv428 h64 h_v531 h_v541 as ⟨v542, s429, hinv429, h_v542⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v526 dropping h_v531 h_v541 hinv428 s428 v531 v541
          store_step with Store.apply_mk_rep s429 v526 v542 _ _ hinv429 h64 h_v526 h_v542 as ⟨v543, s430, hinv430, h_v543⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 dropping h_v526 h_v542 hinv429 s429 v526 v542
          step as ⟨e_v544, he_v544⟩
          store_step with CtorSpec.eo_bvxor.construct s430 e_v544 (by rw [he_v544]; exact empty_args) hinv430 h64 as ⟨v544, s431, hinv431, h_v544⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v543 dropping he_v544 hinv430 e_v544 s430
          store_step with ih.eo__24eo_5ftypeof s431 v9 _ hinv431 h64 (hG.rem hrem) h_v9 as ⟨v545, s432, hinv432, h_v545⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v543 h_v544 dropping hinv431 s431
          store_step with ih.eo__24eo_5fnil s432 v544 v545 _ _ hinv432 h64 (hG.rem hrem) h_v544 h_v545 as ⟨v546, s433, hinv433, h_v546⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 h_v543 dropping h_v544 h_v545 hinv432 s432 v544 v545
          store_step with Store.apply_mk_rep s433 v543 v546 _ _ hinv433 h64 h_v543 h_v546 as ⟨v547, s434, hinv434, h_v547⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 h_v525 dropping h_v543 h_v546 hinv433 s433 v543 v546
          store_step with Store.apply_mk_rep s434 v525 v547 _ _ hinv434 h64 h_v525 h_v547 as ⟨v548, s435, hinv435, h_v548⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 h_v523 dropping h_v525 h_v547 hinv434 s434 v525 v547
          store_step with Store.apply_mk_rep s435 v523 v548 _ _ hinv435 h64 h_v523 h_v548 as ⟨v549, s436, hinv436, h_v549⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v520 dropping h_v523 h_v548 hinv435 s435 v523 v548
          store_step with Store.apply_mk_rep s436 v520 v549 _ _ hinv436 h64 h_v520 h_v549 as ⟨v550, s437, hinv437, h_v550⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 dropping h_v520 h_v549 hinv436 s436 v520 v549
          step as ⟨e_v551, he_v551⟩
          store_step with CtorSpec.eo_bvand.construct s437 e_v551 (by rw [he_v551]; exact empty_args) hinv437 h64 as ⟨v551, s438, hinv438, h_v551⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 dropping he_v551 hinv437 e_v551 s437
          store_step with ih.eo__24eo_5ftypeof s438 v12 _ hinv438 h64 (hG.rem hrem) h_v12 as ⟨v552, s439, hinv439, h_v552⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 dropping hinv438 s438
          store_step with ih.eo__24bv_5fbitwidth s439 v552 _ hinv439 h64 (hG.rem hrem) h_v552 as ⟨v553, s440, hinv440, h_v553⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 dropping h_v552 hinv439 s439 v552
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s440 2#u32 (-2) (by scalar_tac) hinv440 h64 as ⟨v554, s441, hinv441, h_v554⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v553 dropping hinv440 s440
          step as ⟨e_v555, he_v555⟩
          store_step with Store.builtin_spec_add s441 e_v555 (by rw [he_v555]; rfl) h_v553 h_v554 hinv441 h64 as ⟨v555, s442, hinv442, h_v555⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 dropping h_v553 h_v554 he_v555 hinv441 e_v555 s441 v553 v554
          store_step with ih.eo__24eo_5ftypeof s442 v12 _ hinv442 h64 (hG.rem hrem) h_v12 as ⟨v556, s443, hinv443, h_v556⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v555 dropping hinv442 s442
          store_step with ih.eo__24bv_5fbitwidth s443 v556 _ hinv443 h64 (hG.rem hrem) h_v556 as ⟨v557, s444, hinv444, h_v557⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v555 dropping h_v556 hinv443 s443 v556
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s444 2#u32 (-2) (by scalar_tac) hinv444 h64 as ⟨v558, s445, hinv445, h_v558⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v555 h_v557 dropping hinv444 s444
          step as ⟨e_v559, he_v559⟩
          store_step with Store.builtin_spec_add s445 e_v559 (by rw [he_v559]; rfl) h_v557 h_v558 hinv445 h64 as ⟨v559, s446, hinv446, h_v559⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v555 dropping h_v557 h_v558 he_v559 hinv445 e_v559 s445 v557 v558
          step as ⟨e_v560, he_v560⟩
          store_step with CtorSpec.eo_extract.construct s446 e_v560 (by rw [he_v560]; rfl) h_v555 h_v559 hinv446 h64 as ⟨v560, s447, hinv447, h_v560⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 dropping h_v555 h_v559 he_v560 hinv446 e_v560 s446 v555 v559
          step as ⟨e_v561, he_v561⟩
          store_step with CtorSpec.eo_bvxor.construct s447 e_v561 (by rw [he_v561]; exact empty_args) hinv447 h64 as ⟨v561, s448, hinv448, h_v561⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 dropping he_v561 hinv447 e_v561 s447
          store_step with Store.apply_rep s448 v561 v12 _ _ hinv448 h64 h_v561 h_v12 (by ns_tac) (by ns_tac) as ⟨v562, s449, hinv449, h_v562⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 dropping h_v561 hinv448 s448 v561
          step as ⟨e_v563, he_v563⟩
          store_step with CtorSpec.eo_bvxor.construct s449 e_v563 (by rw [he_v563]; exact empty_args) hinv449 h64 as ⟨v563, s450, hinv450, h_v563⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 dropping he_v563 hinv449 e_v563 s449
          store_step with ih.eo__24eo_5ftypeof s450 v12 _ hinv450 h64 (hG.rem hrem) h_v12 as ⟨v564, s451, hinv451, h_v564⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 dropping hinv450 s450
          store_step with ih.eo__24bv_5fbitwidth s451 v564 _ hinv451 h64 (hG.rem hrem) h_v564 as ⟨v565, s452, hinv452, h_v565⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 dropping h_v564 hinv451 s451 v564
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s452 1#u32 (-1) (by scalar_tac) hinv452 h64 as ⟨v566, s453, hinv453, h_v566⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v565 dropping hinv452 s452
          step as ⟨e_v567, he_v567⟩
          store_step with Store.builtin_spec_add s453 e_v567 (by rw [he_v567]; rfl) h_v565 h_v566 hinv453 h64 as ⟨v567, s454, hinv454, h_v567⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 dropping h_v565 h_v566 he_v567 hinv453 e_v567 s453 v565 v566
          step as ⟨e_v568, he_v568⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s454 e_v568 (by rw [he_v568]; rfl) h_v567 hinv454 h64 as ⟨v568, s455, hinv455, h_v568⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 dropping h_v567 he_v568 hinv454 e_v568 s454 v567
          store_step with ih.eo__24eo_5ftypeof s455 v12 _ hinv455 h64 (hG.rem hrem) h_v12 as ⟨v569, s456, hinv456, h_v569⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 dropping hinv455 s455
          store_step with ih.eo__24bv_5fbitwidth s456 v569 _ hinv456 h64 (hG.rem hrem) h_v569 as ⟨v570, s457, hinv457, h_v570⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 dropping h_v569 hinv456 s456 v569
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s457 1#u32 (-1) (by scalar_tac) hinv457 h64 as ⟨v571, s458, hinv458, h_v571⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 h_v570 dropping hinv457 s457
          step as ⟨e_v572, he_v572⟩
          store_step with Store.builtin_spec_add s458 e_v572 (by rw [he_v572]; rfl) h_v570 h_v571 hinv458 h64 as ⟨v572, s459, hinv459, h_v572⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 dropping h_v570 h_v571 he_v572 hinv458 e_v572 s458 v570 v571
          store_step with ih.eo__24eo_5ftypeof s459 v12 _ hinv459 h64 (hG.rem hrem) h_v12 as ⟨v573, s460, hinv460, h_v573⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 h_v572 dropping hinv459 s459
          store_step with ih.eo__24bv_5fbitwidth s460 v573 _ hinv460 h64 (hG.rem hrem) h_v573 as ⟨v574, s461, hinv461, h_v574⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 h_v572 dropping h_v573 hinv460 s460 v573
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s461 1#u32 (-1) (by scalar_tac) hinv461 h64 as ⟨v575, s462, hinv462, h_v575⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 h_v572 h_v574 dropping hinv461 s461
          step as ⟨e_v576, he_v576⟩
          store_step with Store.builtin_spec_add s462 e_v576 (by rw [he_v576]; rfl) h_v574 h_v575 hinv462 h64 as ⟨v576, s463, hinv463, h_v576⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 h_v572 dropping h_v574 h_v575 he_v576 hinv462 e_v576 s462 v574 v575
          step as ⟨e_v577, he_v577⟩
          store_step with CtorSpec.eo_extract.construct s463 e_v577 (by rw [he_v577]; rfl) h_v572 h_v576 hinv463 h64 as ⟨v577, s464, hinv464, h_v577⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 dropping h_v572 h_v576 he_v577 hinv463 e_v577 s463 v572 v576
          store_step with Store.apply_mk_rep s464 v577 v12 _ _ hinv464 h64 h_v577 h_v12 as ⟨v578, s465, hinv465, h_v578⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 h_v568 dropping h_v577 hinv464 s464 v577
          store_step with Store.apply_mk_rep s465 v568 v578 _ _ hinv465 h64 h_v568 h_v578 as ⟨v579, s466, hinv466, h_v579⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v563 dropping h_v568 h_v578 hinv465 s465 v568 v578
          store_step with Store.apply_mk_rep s466 v563 v579 _ _ hinv466 h64 h_v563 h_v579 as ⟨v580, s467, hinv467, h_v580⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 dropping h_v563 h_v579 hinv466 s466 v563 v579
          step as ⟨e_v581, he_v581⟩
          store_step with CtorSpec.eo_bvxor.construct s467 e_v581 (by rw [he_v581]; exact empty_args) hinv467 h64 as ⟨v581, s468, hinv468, h_v581⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v580 dropping he_v581 hinv467 e_v581 s467
          store_step with ih.eo__24eo_5ftypeof s468 v12 _ hinv468 h64 (hG.rem hrem) h_v12 as ⟨v582, s469, hinv469, h_v582⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v580 h_v581 dropping hinv468 s468
          store_step with ih.eo__24eo_5fnil s469 v581 v582 _ _ hinv469 h64 (hG.rem hrem) h_v581 h_v582 as ⟨v583, s470, hinv470, h_v583⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 h_v580 dropping h_v581 h_v582 hinv469 s469 v581 v582
          store_step with Store.apply_mk_rep s470 v580 v583 _ _ hinv470 h64 h_v580 h_v583 as ⟨v584, s471, hinv471, h_v584⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 h_v562 dropping h_v580 h_v583 hinv470 s470 v580 v583
          store_step with Store.apply_mk_rep s471 v562 v584 _ _ hinv471 h64 h_v562 h_v584 as ⟨v585, s472, hinv472, h_v585⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 h_v560 dropping h_v562 h_v584 hinv471 s471 v562 v584
          store_step with Store.apply_mk_rep s472 v560 v585 _ _ hinv472 h64 h_v560 h_v585 as ⟨v586, s473, hinv473, h_v586⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v551 dropping h_v560 h_v585 hinv472 s472 v560 v585
          store_step with Store.apply_mk_rep s473 v551 v586 _ _ hinv473 h64 h_v551 h_v586 as ⟨v587, s474, hinv474, h_v587⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 dropping h_v551 h_v586 hinv473 s473 v551 v586
          step as ⟨e_v588, he_v588⟩
          store_step with CtorSpec.eo_bvand.construct s474 e_v588 (by rw [he_v588]; exact empty_args) hinv474 h64 as ⟨v588, s475, hinv475, h_v588⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 dropping he_v588 hinv474 e_v588 s474
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s475 1#u32 (1) (by scalar_tac) hinv475 h64 as ⟨v589, s476, hinv476, h_v589⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 dropping hinv475 s475
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s476 1#u32 (1) (by scalar_tac) hinv476 h64 as ⟨v590, s477, hinv477, h_v590⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v589 dropping hinv476 s476
          step as ⟨e_v591, he_v591⟩
          store_step with CtorSpec.eo_extract.construct s477 e_v591 (by rw [he_v591]; rfl) h_v589 h_v590 hinv477 h64 as ⟨v591, s478, hinv478, h_v591⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 dropping h_v589 h_v590 he_v591 hinv477 e_v591 s477 v589 v590
          step as ⟨e_v592, he_v592⟩
          store_step with CtorSpec.eo_bvxor.construct s478 e_v592 (by rw [he_v592]; exact empty_args) hinv478 h64 as ⟨v592, s479, hinv479, h_v592⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 dropping he_v592 hinv478 e_v592 s478
          store_step with Store.apply_rep s479 v592 v9 _ _ hinv479 h64 h_v592 h_v9 (by ns_tac) (by ns_tac) as ⟨v593, s480, hinv480, h_v593⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 dropping h_v592 hinv479 s479 v592
          step as ⟨e_v594, he_v594⟩
          store_step with CtorSpec.eo_bvxor.construct s480 e_v594 (by rw [he_v594]; exact empty_args) hinv480 h64 as ⟨v594, s481, hinv481, h_v594⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 dropping he_v594 hinv480 e_v594 s480
          store_step with ih.eo__24eo_5ftypeof s481 v12 _ hinv481 h64 (hG.rem hrem) h_v12 as ⟨v595, s482, hinv482, h_v595⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 dropping hinv481 s481
          store_step with ih.eo__24bv_5fbitwidth s482 v595 _ hinv482 h64 (hG.rem hrem) h_v595 as ⟨v596, s483, hinv483, h_v596⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 dropping h_v595 hinv482 s482 v595
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s483 1#u32 (-1) (by scalar_tac) hinv483 h64 as ⟨v597, s484, hinv484, h_v597⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v596 dropping hinv483 s483
          step as ⟨e_v598, he_v598⟩
          store_step with Store.builtin_spec_add s484 e_v598 (by rw [he_v598]; rfl) h_v596 h_v597 hinv484 h64 as ⟨v598, s485, hinv485, h_v598⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 dropping h_v596 h_v597 he_v598 hinv484 e_v598 s484 v596 v597
          step as ⟨e_v599, he_v599⟩
          store_step with CtorSpec.eo_sign_5fextend.construct s485 e_v599 (by rw [he_v599]; rfl) h_v598 hinv485 h64 as ⟨v599, s486, hinv486, h_v599⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 dropping h_v598 he_v599 hinv485 e_v599 s485 v598
          store_step with ih.eo__24eo_5ftypeof s486 v12 _ hinv486 h64 (hG.rem hrem) h_v12 as ⟨v600, s487, hinv487, h_v600⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 dropping hinv486 s486
          store_step with ih.eo__24bv_5fbitwidth s487 v600 _ hinv487 h64 (hG.rem hrem) h_v600 as ⟨v601, s488, hinv488, h_v601⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 dropping h_v600 hinv487 s487 v600
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s488 1#u32 (-1) (by scalar_tac) hinv488 h64 as ⟨v602, s489, hinv489, h_v602⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 h_v601 dropping hinv488 s488
          step as ⟨e_v603, he_v603⟩
          store_step with Store.builtin_spec_add s489 e_v603 (by rw [he_v603]; rfl) h_v601 h_v602 hinv489 h64 as ⟨v603, s490, hinv490, h_v603⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 dropping h_v601 h_v602 he_v603 hinv489 e_v603 s489 v601 v602
          store_step with ih.eo__24eo_5ftypeof s490 v12 _ hinv490 h64 (hG.rem hrem) h_v12 as ⟨v604, s491, hinv491, h_v604⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 h_v603 dropping hinv490 s490
          store_step with ih.eo__24bv_5fbitwidth s491 v604 _ hinv491 h64 (hG.rem hrem) h_v604 as ⟨v605, s492, hinv492, h_v605⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 h_v603 dropping h_v604 hinv491 s491 v604
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s492 1#u32 (-1) (by scalar_tac) hinv492 h64 as ⟨v606, s493, hinv493, h_v606⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 h_v603 h_v605 dropping hinv492 s492
          step as ⟨e_v607, he_v607⟩
          store_step with Store.builtin_spec_add s493 e_v607 (by rw [he_v607]; rfl) h_v605 h_v606 hinv493 h64 as ⟨v607, s494, hinv494, h_v607⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 h_v603 dropping h_v605 h_v606 he_v607 hinv493 e_v607 s493 v605 v606
          step as ⟨e_v608, he_v608⟩
          store_step with CtorSpec.eo_extract.construct s494 e_v608 (by rw [he_v608]; rfl) h_v603 h_v607 hinv494 h64 as ⟨v608, s495, hinv495, h_v608⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 dropping h_v603 h_v607 he_v608 hinv494 e_v608 s494 v603 v607
          store_step with Store.apply_mk_rep s495 v608 v9 _ _ hinv495 h64 h_v608 h_v9 as ⟨v609, s496, hinv496, h_v609⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 h_v599 dropping h_v608 hinv495 s495 v608
          store_step with Store.apply_mk_rep s496 v599 v609 _ _ hinv496 h64 h_v599 h_v609 as ⟨v610, s497, hinv497, h_v610⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v594 dropping h_v599 h_v609 hinv496 s496 v599 v609
          store_step with Store.apply_mk_rep s497 v594 v610 _ _ hinv497 h64 h_v594 h_v610 as ⟨v611, s498, hinv498, h_v611⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 dropping h_v594 h_v610 hinv497 s497 v594 v610
          step as ⟨e_v612, he_v612⟩
          store_step with CtorSpec.eo_bvxor.construct s498 e_v612 (by rw [he_v612]; exact empty_args) hinv498 h64 as ⟨v612, s499, hinv499, h_v612⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v611 dropping he_v612 hinv498 e_v612 s498
          store_step with ih.eo__24eo_5ftypeof s499 v9 _ hinv499 h64 (hG.rem hrem) h_v9 as ⟨v613, s500, hinv500, h_v613⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v611 h_v612 dropping hinv499 s499
          store_step with ih.eo__24eo_5fnil s500 v612 v613 _ _ hinv500 h64 (hG.rem hrem) h_v612 h_v613 as ⟨v614, s501, hinv501, h_v614⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 h_v611 dropping h_v612 h_v613 hinv500 s500 v612 v613
          store_step with Store.apply_mk_rep s501 v611 v614 _ _ hinv501 h64 h_v611 h_v614 as ⟨v615, s502, hinv502, h_v615⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 h_v593 dropping h_v611 h_v614 hinv501 s501 v611 v614
          store_step with Store.apply_mk_rep s502 v593 v615 _ _ hinv502 h64 h_v593 h_v615 as ⟨v616, s503, hinv503, h_v616⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 h_v591 dropping h_v593 h_v615 hinv502 s502 v593 v615
          store_step with Store.apply_mk_rep s503 v591 v616 _ _ hinv503 h64 h_v591 h_v616 as ⟨v617, s504, hinv504, h_v617⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 dropping h_v591 h_v616 hinv503 s503 v591 v616
          store_step with ih.eo__24eo_5ftypeof s504 v617 _ hinv504 h64 (hG.rem hrem) h_v617 as ⟨v618, s505, hinv505, h_v618⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 h_v588 dropping h_v617 hinv504 s504 v617
          store_step with ih.eo__24eo_5fnil s505 v588 v618 _ _ hinv505 h64 (hG.rem hrem) h_v588 h_v618 as ⟨v619, s506, hinv506, h_v619⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 h_v587 dropping h_v588 h_v618 hinv505 s505 v588 v618
          store_step with Store.apply_mk_rep s506 v587 v619 _ _ hinv506 h64 h_v587 h_v619 as ⟨v620, s507, hinv507, h_v620⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v550 dropping h_v587 h_v619 hinv506 s506 v587 v619
          store_step with Store.apply_mk_rep s507 v550 v620 _ _ hinv507 h64 h_v550 h_v620 as ⟨v621, s508, hinv508, h_v621⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 dropping h_v550 h_v620 hinv507 s507 v550 v620
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s508 1#u32 (1) (by scalar_tac) hinv508 h64 as ⟨v622, s509, hinv509, h_v622⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping hinv508 s508
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s509 1#u32 (-1) (by scalar_tac) hinv509 h64 as ⟨v623, s510, hinv510, h_v623⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v622 dropping hinv509 s509
          store_step with ih.eo__24eo_5ftypeof s510 v12 _ hinv510 h64 (hG.rem hrem) h_v12 as ⟨v624, s511, hinv511, h_v624⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v622 h_v623 dropping hinv510 s510
          store_step with ih.eo__24bv_5fbitwidth s511 v624 _ hinv511 h64 (hG.rem hrem) h_v624 as ⟨v625, s512, hinv512, h_v625⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v622 h_v623 dropping h_v624 hinv511 s511 v624
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s512 2#u32 (-2) (by scalar_tac) hinv512 h64 as ⟨v626, s513, hinv513, h_v626⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v622 h_v623 h_v625 dropping hinv512 s512
          step as ⟨e_v627, he_v627⟩
          store_step with Store.builtin_spec_add s513 e_v627 (by rw [he_v627]; rfl) h_v625 h_v626 hinv513 h64 as ⟨v627, s514, hinv514, h_v627⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v622 h_v623 dropping h_v625 h_v626 he_v627 hinv513 e_v627 s513 v625 v626
          step as ⟨e_v628, he_v628⟩
          store_step with Store.builtin_spec_add s514 e_v628 (by rw [he_v628]; rfl) h_v623 h_v627 hinv514 h64 as ⟨v628, s515, hinv515, h_v628⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v622 dropping h_v623 h_v627 he_v628 hinv514 e_v628 s514 v623 v627
          step as ⟨e_v629, he_v629⟩
          store_step with Store.builtin_spec_add s515 e_v629 (by rw [he_v629]; rfl) h_v622 h_v628 hinv515 h64 as ⟨v629, s516, hinv516, h_v629⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_v622 h_v628 he_v629 hinv515 e_v629 s515 v622 v628
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s516 1#u32 (-1) (by scalar_tac) hinv516 h64 as ⟨v630, s517, hinv517, h_v630⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v629 dropping hinv516 s516
          step as ⟨e_v631, he_v631⟩
          store_step with Store.builtin_spec_add s517 e_v631 (by rw [he_v631]; rfl) h_v629 h_v630 hinv517 h64 as ⟨v631, s518, hinv518, h_v631⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_v629 h_v630 he_v631 hinv517 e_v631 s517 v629 v630
          step as ⟨e_v632, he_v632⟩
          store_step with Store.builtin_spec_is_neg s518 e_v632 (by rw [he_v632]; rfl) h_v631 hinv518 h64 as ⟨v632, s519, hinv519, h_v632⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_v631 he_v632 hinv518 e_v632 s518 v631
          store_step with Store.literal_boolean_spec s519 false hinv519 h64 as ⟨v633, s520, hinv520, h_v633⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v632 dropping hinv519 s519
          have h_req_v649 := (show requires_3_eo__24eo_5fprog_5fbv_2dsmulo_2delim s520 v632 v633 v12 ⦃ r s' => s'.Inv ∧ s520.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
            unfold requires_3_eo__24eo_5fprog_5fbv_2dsmulo_2delim
            have hrem := (hG.rem hrem)
            have hG := Store.Grows.refl s520
            req_same v632 v633 with h_v632 h_v633 using hinv520 hG
            req_stuck h_v632 as hq_v632 using hinv520 hG
            step as ⟨e_v634, he_v634⟩
            store_step with CtorSpec.eo__40_40TypedList_2econs.construct s520 e_v634 (by rw [he_v634]; exact empty_args) hinv520 h64 as ⟨v634, s521, hinv521, h_v634⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_v632 h_v633 he_v634 hinv520 e_v634 s520 v632 v633
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s521 0#u32 (0) (by scalar_tac) hinv521 h64 as ⟨v635, s522, hinv522, h_v635⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 dropping hinv521 s521
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s522 1#u32 (1) (by scalar_tac) hinv522 h64 as ⟨v636, s523, hinv523, h_v636⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 dropping hinv522 s522
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s523 1#u32 (-1) (by scalar_tac) hinv523 h64 as ⟨v637, s524, hinv524, h_v637⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v636 dropping hinv523 s523
            store_step with ih.eo__24eo_5ftypeof s524 v12 _ hinv524 h64 (hG.rem hrem) h_v12 as ⟨v638, s525, hinv525, h_v638⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v636 h_v637 dropping hinv524 s524
            store_step with ih.eo__24bv_5fbitwidth s525 v638 _ hinv525 h64 (hG.rem hrem) h_v638 as ⟨v639, s526, hinv526, h_v639⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v636 h_v637 dropping h_v638 hinv525 s525 v638
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s526 2#u32 (-2) (by scalar_tac) hinv526 h64 as ⟨v640, s527, hinv527, h_v640⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v636 h_v637 h_v639 dropping hinv526 s526
            step as ⟨e_v641, he_v641⟩
            store_step with Store.builtin_spec_add s527 e_v641 (by rw [he_v641]; rfl) h_v639 h_v640 hinv527 h64 as ⟨v641, s528, hinv528, h_v641⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v636 h_v637 dropping h_v639 h_v640 he_v641 hinv527 e_v641 s527 v639 v640
            step as ⟨e_v642, he_v642⟩
            store_step with Store.builtin_spec_add s528 e_v642 (by rw [he_v642]; rfl) h_v637 h_v641 hinv528 h64 as ⟨v642, s529, hinv529, h_v642⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v636 dropping h_v637 h_v641 he_v642 hinv528 e_v642 s528 v637 v641
            step as ⟨e_v643, he_v643⟩
            store_step with Store.builtin_spec_add s529 e_v643 (by rw [he_v643]; rfl) h_v636 h_v642 hinv529 h64 as ⟨v643, s530, hinv530, h_v643⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 dropping h_v636 h_v642 he_v643 hinv529 e_v643 s529 v636 v642
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s530 1#u32 (-1) (by scalar_tac) hinv530 h64 as ⟨v644, s531, hinv531, h_v644⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 h_v643 dropping hinv530 s530
            step as ⟨e_v645, he_v645⟩
            store_step with Store.builtin_spec_add s531 e_v645 (by rw [he_v645]; rfl) h_v643 h_v644 hinv531 h64 as ⟨v645, s532, hinv532, h_v645⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v634 h_v635 dropping h_v643 h_v644 he_v645 hinv531 e_v645 s531 v643 v644
            step as ⟨e_v646, he_v646⟩
            store_step with Store.builtin_spec_list_repeat n ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s532 e_v646 (by rw [he_v646]; rfl) h_v634 h_v635 h_v645 hinv532 h64 (hG.rem hrem) op_not_left_eo__40_40TypedList_2econs as ⟨v646, s533, hinv533, h_v646⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_v634 h_v635 h_v645 he_v646 hinv532 e_v646 s532 v634 v635 v645
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s533 1#u32 (1) (by scalar_tac) hinv533 h64 as ⟨v647, s534, hinv534, h_v647⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v646 dropping hinv533 s533
            store_step with ih.eo__24iota_5frec s534 v646 v647 _ _ hinv534 h64 (hG.rem hrem) h_v646 h_v647 as ⟨v648, s535, hinv535, h_v648⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_v646 h_v647 hinv534 s534 v646 v647
            req_done hinv535 hG with h_v648 using hq_v632)
          store_step with h_req_v649 as ⟨v649, s536, hinv536, h_v649⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 dropping h_req_v649 h_v632 h_v633 hinv520 s520 v632 v633
          store_step with ih.eo__24eo_5ftypeof s536 v12 _ hinv536 h64 (hG.rem hrem) h_v12 as ⟨v650, s537, hinv537, h_v650⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v649 dropping hinv536 s536
          store_step with ih.eo__24bv_5fbitwidth s537 v650 _ hinv537 h64 (hG.rem hrem) h_v650 as ⟨v651, s538, hinv538, h_v651⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v649 dropping h_v650 hinv537 s537 v650
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_neg_u32_spec s538 2#u32 (-2) (by scalar_tac) hinv538 h64 as ⟨v652, s539, hinv539, h_v652⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v649 h_v651 dropping hinv538 s538
          step as ⟨e_v653, he_v653⟩
          store_step with Store.builtin_spec_add s539 e_v653 (by rw [he_v653]; rfl) h_v651 h_v652 hinv539 h64 as ⟨v653, s540, hinv540, h_v653⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 h_v459 h_v484 h_v519 h_v621 h_v649 dropping h_v651 h_v652 he_v653 hinv539 e_v653 s539 v651 v652
          store_step with ih.eo__24bv_5fsmulo_5felim_5frec s540 v459 v484 v519 v621 v649 v653 _ _ _ _ _ _ hinv540 h64 (hG.rem hrem) h_v459 h_v484 h_v519 h_v621 h_v649 h_v653 as ⟨v654, s541, hinv541, h_v654⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 dropping h_v459 h_v484 h_v519 h_v621 h_v649 h_v653 hinv540 s540 v459 v484 v519 v621 v649 v653
          store_step with ih.eo__24eo_5ftypeof s541 v654 _ hinv541 h64 (hG.rem hrem) h_v654 as ⟨v655, s542, hinv542, h_v655⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 h_v434 dropping h_v654 hinv541 s541 v654
          store_step with ih.eo__24eo_5fnil s542 v434 v655 _ _ hinv542 h64 (hG.rem hrem) h_v434 h_v655 as ⟨v656, s543, hinv543, h_v656⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 h_v433 dropping h_v434 h_v655 hinv542 s542 v434 v655
          store_step with Store.apply_mk_rep s543 v433 v656 _ _ hinv543 h64 h_v433 h_v656 as ⟨v657, s544, hinv544, h_v657⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 h_v346 dropping h_v433 h_v656 hinv543 s543 v433 v656
          store_step with Store.apply_mk_rep s544 v346 v657 _ _ hinv544 h64 h_v346 h_v657 as ⟨v658, s545, hinv545, h_v658⟩ growing hG carrying h_v2 h_v9 h_v12 h_v124 dropping h_v346 h_v657 hinv544 s544 v346 v657
          store_step with Store.apply_mk_rep s545 v124 v658 _ _ hinv545 h64 h_v124 h_v658 as ⟨v659, s546, hinv546, h_v659⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v124 h_v658 hinv545 s545 v124 v658
          try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
          store_step with Store.literal_binary_u32_spec s546 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv546 h64 as ⟨v660, s547, hinv547, h_v660⟩ growing hG carrying h_v2 h_v9 h_v12 h_v659 dropping hinv546 s546
          store_step with Store.apply_mk_rep s547 v659 v660 _ _ hinv547 h64 h_v659 h_v660 as ⟨v661, s548, hinv548, h_v661⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v659 h_v660 hinv547 s547 v659 v660
          ite_done hinv548 hG with (eo_ite_false_rep _ hx_35 h_v661)
        · ite_branch hbv_35
          ite_stuck hinv10 hG with hx_35)
      store_step with h_ite_v662 as ⟨v662, s11, hinv11, h_v662⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_ite_v662 h_v34 v34
      ite_done hinv11 hG with (eo_ite_false_rep _ hx_18 h_v662)
    · ite_branch hbv_18
      ite_stuck hinv6 hG with hx_18)
  store_step with h_ite_v663 as ⟨v663, s7, hinv7, h_v663⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_ite_v663 h_v17 hinv6 s6 v17
  have h_req_v670 := (show requires_56_eo__24eo_5fprog_5fbv_2dsmulo_2delim s7 v663 v2 v12 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_56_eo__24eo_5fprog_5fbv_2dsmulo_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v663 v2 with h_v663 h_v2 using hinv7 hG
    req_stuck h_v663 as hq_v663 using hinv7 hG
    step as ⟨e_v664, he_v664⟩
    store_step with CtorSpec.eo__3d.construct s7 e_v664 (by rw [he_v664]; exact empty_args) hinv7 h64 as ⟨v664, s8, hinv8, h_v664⟩ growing hG carrying h_v2 h_v9 h_v12 dropping h_v663 he_v664 hinv7 e_v664 s7 v663
    step as ⟨e_v665, he_v665⟩
    store_step with CtorSpec.eo_bvsmulo.construct s8 e_v665 (by rw [he_v665]; exact empty_args) hinv8 h64 as ⟨v665, s9, hinv9, h_v665⟩ growing hG carrying h_v2 h_v9 h_v12 h_v664 dropping he_v665 hinv8 e_v665 s8
    store_step with Store.apply_rep s9 v665 v12 _ _ hinv9 h64 h_v665 h_v12 (by ns_tac) (by ns_tac) as ⟨v666, s10, hinv10, h_v666⟩ growing hG carrying h_v2 h_v9 h_v664 dropping h_v12 h_v665 hinv9 s9 v12 v665
    store_step with Store.apply_rep s10 v666 v9 _ _ hinv10 h64 h_v666 h_v9 (by ns_tac) (by ns_tac) as ⟨v667, s11, hinv11, h_v667⟩ growing hG carrying h_v2 h_v664 dropping h_v666 h_v9 hinv10 s10 v666 v9
    store_step with Store.apply_rep s11 v664 v667 _ _ hinv11 h64 h_v664 h_v667 (by ns_tac) (by ns_tac) as ⟨v668, s12, hinv12, h_v668⟩ growing hG carrying h_v2 dropping h_v664 h_v667 hinv11 s11 v664 v667
    store_step with Store.apply_rep s12 v668 v2 _ _ hinv12 h64 h_v668 h_v2 (by ns_tac) (by ns_tac) as ⟨v669, s13, hinv13, h_v669⟩ growing hG carrying dropping h_v2 h_v668 hinv12 s12 v2 v668
    req_done hinv13 hG with h_v669 using hq_v663)
  store_step with h_req_v670 as ⟨v670, s14, hinv14, h_v670⟩ growing hG carrying dropping h_req_v670 h_v12 h_v2 h_v663 h_v9 hinv7 s7 v12 v2 v663 v9
  case_done hinv14 hG with h_v670 in EoCases.__eo_prog_bv_smulo_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__eo_prog_bv_smulo_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsmulo_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_smulo_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_smulo_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_smulo_elim
  unfold EoCases.__eo_prog_bv_smulo_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsmulo_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dsmulo_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_smulo_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsmulo_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dsmulo_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsmulo_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_smulo_elim.case_0

theorem eo__24eo_5fprog_5fbv_2dsmulo_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsmulo_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dsmulo_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsmulo_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_smulo_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsmulo_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

set_option maxHeartbeats 2730000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_srem_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_srem_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_srem_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v11 h_v20 he_v21 hinv4 e_v21 s4 v11 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvsrem.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v23 a1 _ _ hinv7 h64 h_v23 h_a1 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v23 hinv7 s7 v23
  store_step with Store.apply_rep s8 v21 v24 _ _ hinv8 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v21 h_v24 hinv8 s8 v21 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v26 (by rw [he_v26]; exact empty_args) hinv9 h64 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping he_v26 hinv9 e_v26 s9
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping he_v27 hinv10 e_v27 s10
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_extract.construct s11 e_v28 (by rw [he_v28]; rfl) h_a2 h_a2 hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping he_v28 hinv11 e_v28 s11
  store_step with Store.apply_rep s12 v28 a0 _ _ hinv12 h64 h_v28 h_a0 (by ns_tac) (by ns_tac) as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v28 hinv12 s12 v28
  store_step with Store.apply_rep s13 v27 v29 _ _ hinv13 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v27 h_v29 hinv13 s13 v27 v29
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 1#u32 (1) (by scalar_tac) hinv14 h64 as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v30 dropping hinv14 s14
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s15 e_v32 (by rw [he_v32]; rfl) h_v31 hinv15 h64 as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v30 dropping h_v31 he_v32 hinv15 e_v32 s15 v31
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 1#u32 (1) (by scalar_tac) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v30 h_v32 dropping hinv16 s16
  store_step with Store.apply_rep s17 v32 v33 _ _ hinv17 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v30 dropping h_v32 h_v33 hinv17 s17 v32 v33
  store_step with Store.apply_rep s18 v30 v34 _ _ hinv18 h64 h_v30 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v30 h_v34 hinv18 s18 v30 v34
  store_step with Store.apply_rep s19 v26 v35 _ _ hinv19 h64 h_v26 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v26 h_v35 hinv19 s19 v26 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_bvneg.construct s20 e_v37 (by rw [he_v37]; exact empty_args) hinv20 h64 as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 dropping he_v37 hinv20 e_v37 s20
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_bvurem.construct s21 e_v38 (by rw [he_v38]; exact empty_args) hinv21 h64 as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 dropping he_v38 hinv21 e_v38 s21
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_ite.construct s22 e_v39 (by rw [he_v39]; exact empty_args) hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 dropping he_v39 hinv22 e_v39 s22
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s23 e_v40 (by rw [he_v40]; exact empty_args) hinv23 h64 as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 dropping he_v40 hinv23 e_v40 s23
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_extract.construct s24 e_v41 (by rw [he_v41]; rfl) h_a2 h_a2 hinv24 h64 as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 h_v40 dropping he_v41 hinv24 e_v41 s24
  store_step with Store.apply_rep s25 v41 a0 _ _ hinv25 h64 h_v41 h_a0 (by ns_tac) (by ns_tac) as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 h_v40 dropping h_v41 hinv25 s25 v41
  store_step with Store.apply_rep s26 v40 v42 _ _ hinv26 h64 h_v40 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 dropping h_v40 h_v42 hinv26 s26 v40 v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s27 1#u32 (1) (by scalar_tac) hinv27 h64 as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 h_v43 dropping hinv27 s27
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s28 e_v45 (by rw [he_v45]; rfl) h_v44 hinv28 h64 as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 h_v43 dropping h_v44 he_v45 hinv28 e_v45 s28 v44
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s29 1#u32 (1) (by scalar_tac) hinv29 h64 as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 h_v43 h_v45 dropping hinv29 s29
  store_step with Store.apply_rep s30 v45 v46 _ _ hinv30 h64 h_v45 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 h_v43 dropping h_v45 h_v46 hinv30 s30 v45 v46
  store_step with Store.apply_rep s31 v43 v47 _ _ hinv31 h64 h_v43 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v39 dropping h_v43 h_v47 hinv31 s31 v43 v47
  store_step with Store.apply_rep s32 v39 v48 _ _ hinv32 h64 h_v39 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 dropping h_v39 h_v48 hinv32 s32 v39 v48
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_bvneg.construct s33 e_v50 (by rw [he_v50]; exact empty_args) hinv33 h64 as ⟨v50, s34, hinv34, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v49 dropping he_v50 hinv33 e_v50 s33
  store_step with Store.apply_rep s34 v50 a0 _ _ hinv34 h64 h_v50 h_a0 (by ns_tac) (by ns_tac) as ⟨v51, s35, hinv35, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 h_v49 dropping h_v50 hinv34 s34 v50
  store_step with Store.apply_rep s35 v49 v51 _ _ hinv35 h64 h_v49 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s36, hinv36, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 dropping h_v49 h_v51 hinv35 s35 v49 v51
  store_step with Store.apply_rep s36 v52 a0 _ _ hinv36 h64 h_v52 h_a0 (by ns_tac) (by ns_tac) as ⟨v53, s37, hinv37, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v38 dropping h_v52 hinv36 s36 v52
  store_step with Store.apply_rep s37 v38 v53 _ _ hinv37 h64 h_v38 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s38, hinv38, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 dropping h_v38 h_v53 hinv37 s37 v38 v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_ite.construct s38 e_v55 (by rw [he_v55]; exact empty_args) hinv38 h64 as ⟨v55, s39, hinv39, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 dropping he_v55 hinv38 e_v55 s38
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__3d.construct s39 e_v56 (by rw [he_v56]; exact empty_args) hinv39 h64 as ⟨v56, s40, hinv40, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 dropping he_v56 hinv39 e_v56 s39
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_extract.construct s40 e_v57 (by rw [he_v57]; rfl) h_a2 h_a2 hinv40 h64 as ⟨v57, s41, hinv41, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 h_v56 dropping he_v57 hinv40 e_v57 s40
  store_step with Store.apply_rep s41 v57 a1 _ _ hinv41 h64 h_v57 h_a1 (by ns_tac) (by ns_tac) as ⟨v58, s42, hinv42, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 h_v56 dropping h_v57 hinv41 s41 v57
  store_step with Store.apply_rep s42 v56 v58 _ _ hinv42 h64 h_v56 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s43, hinv43, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 dropping h_v56 h_v58 hinv42 s42 v56 v58
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s43 1#u32 (1) (by scalar_tac) hinv43 h64 as ⟨v60, s44, hinv44, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 h_v59 dropping hinv43 s43
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s44 e_v61 (by rw [he_v61]; rfl) h_v60 hinv44 h64 as ⟨v61, s45, hinv45, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 h_v59 dropping h_v60 he_v61 hinv44 e_v61 s44 v60
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s45 1#u32 (1) (by scalar_tac) hinv45 h64 as ⟨v62, s46, hinv46, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 h_v59 h_v61 dropping hinv45 s45
  store_step with Store.apply_rep s46 v61 v62 _ _ hinv46 h64 h_v61 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s47, hinv47, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 h_v59 dropping h_v61 h_v62 hinv46 s46 v61 v62
  store_step with Store.apply_rep s47 v59 v63 _ _ hinv47 h64 h_v59 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s48, hinv48, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v55 dropping h_v59 h_v63 hinv47 s47 v59 v63
  store_step with Store.apply_rep s48 v55 v64 _ _ hinv48 h64 h_v55 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s49, hinv49, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 dropping h_v55 h_v64 hinv48 s48 v55 v64
  step as ⟨e_v66, he_v66⟩
  store_step with CtorSpec.eo_bvneg.construct s49 e_v66 (by rw [he_v66]; exact empty_args) hinv49 h64 as ⟨v66, s50, hinv50, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v65 dropping he_v66 hinv49 e_v66 s49
  store_step with Store.apply_rep s50 v66 a1 _ _ hinv50 h64 h_v66 h_a1 (by ns_tac) (by ns_tac) as ⟨v67, s51, hinv51, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 h_v65 dropping h_v66 hinv50 s50 v66
  store_step with Store.apply_rep s51 v65 v67 _ _ hinv51 h64 h_v65 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s52, hinv52, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 dropping h_v65 h_v67 hinv51 s51 v65 v67
  store_step with Store.apply_rep s52 v68 a1 _ _ hinv52 h64 h_v68 h_a1 (by ns_tac) (by ns_tac) as ⟨v69, s53, hinv53, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 h_v54 dropping h_v68 hinv52 s52 v68
  store_step with Store.apply_rep s53 v54 v69 _ _ hinv53 h64 h_v54 h_v69 (by ns_tac) (by ns_tac) as ⟨v70, s54, hinv54, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 h_v37 dropping h_v54 h_v69 hinv53 s53 v54 v69
  store_step with Store.apply_rep s54 v37 v70 _ _ hinv54 h64 h_v37 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s55, hinv55, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v36 dropping h_v37 h_v70 hinv54 s54 v37 v70
  store_step with Store.apply_rep s55 v36 v71 _ _ hinv55 h64 h_v36 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s56, hinv56, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v36 h_v71 hinv55 s55 v36 v71
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_bvurem.construct s56 e_v73 (by rw [he_v73]; exact empty_args) hinv56 h64 as ⟨v73, s57, hinv57, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 dropping he_v73 hinv56 e_v73 s56
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_ite.construct s57 e_v74 (by rw [he_v74]; exact empty_args) hinv57 h64 as ⟨v74, s58, hinv58, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 dropping he_v74 hinv57 e_v74 s57
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo__3d.construct s58 e_v75 (by rw [he_v75]; exact empty_args) hinv58 h64 as ⟨v75, s59, hinv59, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 dropping he_v75 hinv58 e_v75 s58
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_extract.construct s59 e_v76 (by rw [he_v76]; rfl) h_a2 h_a2 hinv59 h64 as ⟨v76, s60, hinv60, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 h_v75 dropping he_v76 hinv59 e_v76 s59
  store_step with Store.apply_rep s60 v76 a0 _ _ hinv60 h64 h_v76 h_a0 (by ns_tac) (by ns_tac) as ⟨v77, s61, hinv61, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 h_v75 dropping h_v76 hinv60 s60 v76
  store_step with Store.apply_rep s61 v75 v77 _ _ hinv61 h64 h_v75 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s62, hinv62, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 dropping h_v75 h_v77 hinv61 s61 v75 v77
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s62 1#u32 (1) (by scalar_tac) hinv62 h64 as ⟨v79, s63, hinv63, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 h_v78 dropping hinv62 s62
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s63 e_v80 (by rw [he_v80]; rfl) h_v79 hinv63 h64 as ⟨v80, s64, hinv64, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 h_v78 dropping h_v79 he_v80 hinv63 e_v80 s63 v79
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s64 1#u32 (1) (by scalar_tac) hinv64 h64 as ⟨v81, s65, hinv65, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 h_v78 h_v80 dropping hinv64 s64
  store_step with Store.apply_rep s65 v80 v81 _ _ hinv65 h64 h_v80 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s66, hinv66, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 h_v78 dropping h_v80 h_v81 hinv65 s65 v80 v81
  store_step with Store.apply_rep s66 v78 v82 _ _ hinv66 h64 h_v78 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s67, hinv67, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v74 dropping h_v78 h_v82 hinv66 s66 v78 v82
  store_step with Store.apply_rep s67 v74 v83 _ _ hinv67 h64 h_v74 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s68, hinv68, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 dropping h_v74 h_v83 hinv67 s67 v74 v83
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_bvneg.construct s68 e_v85 (by rw [he_v85]; exact empty_args) hinv68 h64 as ⟨v85, s69, hinv69, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v84 dropping he_v85 hinv68 e_v85 s68
  store_step with Store.apply_rep s69 v85 a0 _ _ hinv69 h64 h_v85 h_a0 (by ns_tac) (by ns_tac) as ⟨v86, s70, hinv70, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 h_v84 dropping h_v85 hinv69 s69 v85
  store_step with Store.apply_rep s70 v84 v86 _ _ hinv70 h64 h_v84 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s71, hinv71, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v72 h_v73 dropping h_v84 h_v86 hinv70 s70 v84 v86
  store_step with Store.apply_rep s71 v87 a0 _ _ hinv71 h64 h_v87 h_a0 (by ns_tac) (by ns_tac) as ⟨v88, s72, hinv72, h_v88⟩ growing hG carrying h_a1 h_a2 h_v25 h_v72 h_v73 dropping h_a0 h_v87 hinv71 s71 v87
  store_step with Store.apply_rep s72 v73 v88 _ _ hinv72 h64 h_v73 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s73, hinv73, h_v89⟩ growing hG carrying h_a1 h_a2 h_v25 h_v72 dropping h_v73 h_v88 hinv72 s72 v73 v88
  step as ⟨e_v90, he_v90⟩
  store_step with CtorSpec.eo_ite.construct s73 e_v90 (by rw [he_v90]; exact empty_args) hinv73 h64 as ⟨v90, s74, hinv74, h_v90⟩ growing hG carrying h_a1 h_a2 h_v25 h_v72 h_v89 dropping he_v90 hinv73 e_v90 s73
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo__3d.construct s74 e_v91 (by rw [he_v91]; exact empty_args) hinv74 h64 as ⟨v91, s75, hinv75, h_v91⟩ growing hG carrying h_a1 h_a2 h_v25 h_v72 h_v89 h_v90 dropping he_v91 hinv74 e_v91 s74
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_extract.construct s75 e_v92 (by rw [he_v92]; rfl) h_a2 h_a2 hinv75 h64 as ⟨v92, s76, hinv76, h_v92⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 h_v91 dropping h_a2 he_v92 hinv75 e_v92 s75
  store_step with Store.apply_rep s76 v92 a1 _ _ hinv76 h64 h_v92 h_a1 (by ns_tac) (by ns_tac) as ⟨v93, s77, hinv77, h_v93⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 h_v91 dropping h_v92 hinv76 s76 v92
  store_step with Store.apply_rep s77 v91 v93 _ _ hinv77 h64 h_v91 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s78, hinv78, h_v94⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 dropping h_v91 h_v93 hinv77 s77 v91 v93
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s78 1#u32 (1) (by scalar_tac) hinv78 h64 as ⟨v95, s79, hinv79, h_v95⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 h_v94 dropping hinv78 s78
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s79 e_v96 (by rw [he_v96]; rfl) h_v95 hinv79 h64 as ⟨v96, s80, hinv80, h_v96⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 h_v94 dropping h_v95 he_v96 hinv79 e_v96 s79 v95
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s80 1#u32 (1) (by scalar_tac) hinv80 h64 as ⟨v97, s81, hinv81, h_v97⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 h_v94 h_v96 dropping hinv80 s80
  store_step with Store.apply_rep s81 v96 v97 _ _ hinv81 h64 h_v96 h_v97 (by ns_tac) (by ns_tac) as ⟨v98, s82, hinv82, h_v98⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 h_v94 dropping h_v96 h_v97 hinv81 s81 v96 v97
  store_step with Store.apply_rep s82 v94 v98 _ _ hinv82 h64 h_v94 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s83, hinv83, h_v99⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v90 dropping h_v94 h_v98 hinv82 s82 v94 v98
  store_step with Store.apply_rep s83 v90 v99 _ _ hinv83 h64 h_v90 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s84, hinv84, h_v100⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 dropping h_v90 h_v99 hinv83 s83 v90 v99
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_bvneg.construct s84 e_v101 (by rw [he_v101]; exact empty_args) hinv84 h64 as ⟨v101, s85, hinv85, h_v101⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v100 dropping he_v101 hinv84 e_v101 s84
  store_step with Store.apply_rep s85 v101 a1 _ _ hinv85 h64 h_v101 h_a1 (by ns_tac) (by ns_tac) as ⟨v102, s86, hinv86, h_v102⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 h_v100 dropping h_v101 hinv85 s85 v101
  store_step with Store.apply_rep s86 v100 v102 _ _ hinv86 h64 h_v100 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s87, hinv87, h_v103⟩ growing hG carrying h_a1 h_v25 h_v72 h_v89 dropping h_v100 h_v102 hinv86 s86 v100 v102
  store_step with Store.apply_rep s87 v103 a1 _ _ hinv87 h64 h_v103 h_a1 (by ns_tac) (by ns_tac) as ⟨v104, s88, hinv88, h_v104⟩ growing hG carrying h_v25 h_v72 h_v89 dropping h_a1 h_v103 hinv87 s87 v103
  store_step with Store.apply_rep s88 v89 v104 _ _ hinv88 h64 h_v89 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s89, hinv89, h_v105⟩ growing hG carrying h_v25 h_v72 dropping h_v104 h_v89 hinv88 s88 v104 v89
  store_step with Store.apply_rep s89 v72 v105 _ _ hinv89 h64 h_v72 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s90, hinv90, h_v106⟩ growing hG carrying h_v25 dropping h_v105 h_v72 hinv89 s89 v105 v72
  store_step with Store.apply_rep s90 v25 v106 _ _ hinv90 h64 h_v25 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s91, hinv91, h_v107⟩ growing hG carrying dropping h_v106 h_v25 hinv90 s90 v106 v25
  case_done hinv91 hG with h_v107 in EoCases.__eo_prog_bv_srem_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_srem_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsrem_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_srem_eliminate.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_srem_eliminate
  unfold EoCases.__eo_prog_bv_srem_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsrem_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_srem_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsrem_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dsrem_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_srem_eliminate x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsrem_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sub_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sub_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvsub.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvadd.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v5 hinv6 s6 v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_bvadd.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 dropping he_v7 hinv7 e_v7 s7
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvneg.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a1 _ _ hinv9 h64 h_v8 h_a1 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v4 h_v6 h_v7 dropping h_a1 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v4 h_v6 dropping h_v7 h_v9 hinv10 s10 v7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_bvadd.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v4 h_v6 h_v10 dropping he_v11 hinv11 e_v11 s11
  store_step with ih.eo__24eo_5ftypeof s12 a0 _ hinv12 h64 (hG.rem hrem) h_a0 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v4 h_v6 h_v10 h_v11 dropping h_a0 hinv12 s12
  store_step with ih.eo__24eo_5fnil s13 v11 v12 _ _ hinv13 h64 (hG.rem hrem) h_v11 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v4 h_v6 h_v10 dropping h_v11 h_v12 hinv13 s13 v11 v12
  store_step with Store.apply_mk_rep s14 v10 v13 _ _ hinv14 h64 h_v10 h_v13 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_v4 h_v6 dropping h_v10 h_v13 hinv14 s14 v10 v13
  store_step with Store.apply_mk_rep s15 v6 v14 _ _ hinv15 h64 h_v6 h_v14 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_v4 dropping h_v14 h_v6 hinv15 s15 v14 v6
  store_step with Store.apply_mk_rep s16 v4 v15 _ _ hinv16 h64 h_v4 h_v15 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying dropping h_v15 h_v4 hinv16 s16 v15 v4
  case_done hinv17 hG with h_v16 in EoCases.__eo_prog_bv_sub_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_sub_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsub_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_sub_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sub_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sub_eliminate
  unfold EoCases.__eo_prog_bv_sub_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dsub_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dsub_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sub_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsub_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dsub_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_sub_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dsub_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsub_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dsub_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsub_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_sub_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsub_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_uaddo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_uaddo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v10 h_v11 h_v12 he_v13 hinv2 e_v13 s2 v10 v11 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvuaddo.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping he_v14 hinv3 e_v14 s3
  store_step with Store.apply_rep s4 v14 a0 _ _ hinv4 h64 h_v14 h_a0 (by ns_tac) (by ns_tac) as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping h_v14 hinv4 s4 v14
  store_step with Store.apply_rep s5 v15 a1 _ _ hinv5 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping h_v15 hinv5 s5 v15
  store_step with Store.apply_rep s6 v13 v16 _ _ hinv6 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v16 hinv6 s6 v13 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v18 (by rw [he_v18]; exact empty_args) hinv7 h64 as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv7 e_v18 s7
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_extract.construct s8 e_v19 (by rw [he_v19]; rfl) h_a2 h_a2 hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 dropping h_a2 he_v19 hinv8 e_v19 s8
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_bvadd.construct s9 e_v20 (by rw [he_v20]; exact empty_args) hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 dropping he_v20 hinv9 e_v20 s9
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_concat.construct s10 e_v21 (by rw [he_v21]; exact empty_args) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 dropping he_v21 hinv10 e_v21 s10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v21 dropping hinv11 s11
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s12 e_v23 (by rw [he_v23]; rfl) h_v22 hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v21 dropping h_v22 he_v23 hinv12 e_v23 s12 v22
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 0#u32 (0) (by scalar_tac) hinv13 h64 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v21 h_v23 dropping hinv13 s13
  store_step with Store.apply_rep s14 v23 v24 _ _ hinv14 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v21 dropping h_v23 h_v24 hinv14 s14 v23 v24
  store_step with Store.apply_rep s15 v21 v25 _ _ hinv15 h64 h_v21 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 dropping h_v21 h_v25 hinv15 s15 v21 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_concat.construct s16 e_v27 (by rw [he_v27]; exact empty_args) hinv16 h64 as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v26 dropping he_v27 hinv16 e_v27 s16
  store_step with Store.apply_rep s17 v27 a0 _ _ hinv17 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v26 dropping h_v27 hinv17 s17 v27
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s18 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv18 h64 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v26 h_v28 dropping hinv18 s18
  store_step with Store.apply_rep s19 v28 v29 _ _ hinv19 h64 h_v28 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 h_v26 dropping h_v28 h_v29 hinv19 s19 v28 v29
  store_step with Store.apply_rep s20 v26 v30 _ _ hinv20 h64 h_v26 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v20 dropping h_v26 h_v30 hinv20 s20 v26 v30
  store_step with Store.apply_rep s21 v20 v31 _ _ hinv21 h64 h_v20 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 dropping h_v20 h_v31 hinv21 s21 v20 v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_bvadd.construct s22 e_v33 (by rw [he_v33]; exact empty_args) hinv22 h64 as ⟨v33, s23, hinv23, h_v33⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 dropping he_v33 hinv22 e_v33 s22
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_concat.construct s23 e_v34 (by rw [he_v34]; exact empty_args) hinv23 h64 as ⟨v34, s24, hinv24, h_v34⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 dropping he_v34 hinv23 e_v34 s23
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s24 1#u32 (1) (by scalar_tac) hinv24 h64 as ⟨v35, s25, hinv25, h_v35⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 h_v34 dropping hinv24 s24
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s25 e_v36 (by rw [he_v36]; rfl) h_v35 hinv25 h64 as ⟨v36, s26, hinv26, h_v36⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 h_v34 dropping h_v35 he_v36 hinv25 e_v36 s25 v35
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s26 0#u32 (0) (by scalar_tac) hinv26 h64 as ⟨v37, s27, hinv27, h_v37⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 h_v34 h_v36 dropping hinv26 s26
  store_step with Store.apply_rep s27 v36 v37 _ _ hinv27 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s28, hinv28, h_v38⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 h_v34 dropping h_v36 h_v37 hinv27 s27 v36 v37
  store_step with Store.apply_rep s28 v34 v38 _ _ hinv28 h64 h_v34 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s29, hinv29, h_v39⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 dropping h_v34 h_v38 hinv28 s28 v34 v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_concat.construct s29 e_v40 (by rw [he_v40]; exact empty_args) hinv29 h64 as ⟨v40, s30, hinv30, h_v40⟩ growing hG carrying h_a0 h_a1 h_v17 h_v18 h_v19 h_v32 h_v33 h_v39 dropping he_v40 hinv29 e_v40 s29
  store_step with Store.apply_rep s30 v40 a1 _ _ hinv30 h64 h_v40 h_a1 (by ns_tac) (by ns_tac) as ⟨v41, s31, hinv31, h_v41⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v33 h_v39 dropping h_a1 h_v40 hinv30 s30 v40
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s31 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv31 h64 as ⟨v42, s32, hinv32, h_v42⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v33 h_v39 h_v41 dropping hinv31 s31
  store_step with Store.apply_rep s32 v41 v42 _ _ hinv32 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s33, hinv33, h_v43⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v33 h_v39 dropping h_v41 h_v42 hinv32 s32 v41 v42
  store_step with Store.apply_rep s33 v39 v43 _ _ hinv33 h64 h_v39 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s34, hinv34, h_v44⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v33 dropping h_v39 h_v43 hinv33 s33 v39 v43
  store_step with Store.apply_rep s34 v33 v44 _ _ hinv34 h64 h_v33 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s35, hinv35, h_v45⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 dropping h_v33 h_v44 hinv34 s34 v33 v44
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo_bvadd.construct s35 e_v46 (by rw [he_v46]; exact empty_args) hinv35 h64 as ⟨v46, s36, hinv36, h_v46⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 dropping he_v46 hinv35 e_v46 s35
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_concat.construct s36 e_v47 (by rw [he_v47]; exact empty_args) hinv36 h64 as ⟨v47, s37, hinv37, h_v47⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 dropping he_v47 hinv36 e_v47 s36
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s37 1#u32 (1) (by scalar_tac) hinv37 h64 as ⟨v48, s38, hinv38, h_v48⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v47 dropping hinv37 s37
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s38 e_v49 (by rw [he_v49]; rfl) h_v48 hinv38 h64 as ⟨v49, s39, hinv39, h_v49⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v47 dropping h_v48 he_v49 hinv38 e_v49 s38 v48
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s39 0#u32 (0) (by scalar_tac) hinv39 h64 as ⟨v50, s40, hinv40, h_v50⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v47 h_v49 dropping hinv39 s39
  store_step with Store.apply_rep s40 v49 v50 _ _ hinv40 h64 h_v49 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s41, hinv41, h_v51⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v47 dropping h_v49 h_v50 hinv40 s40 v49 v50
  store_step with Store.apply_rep s41 v47 v51 _ _ hinv41 h64 h_v47 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s42, hinv42, h_v52⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 dropping h_v47 h_v51 hinv41 s41 v47 v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_concat.construct s42 e_v53 (by rw [he_v53]; exact empty_args) hinv42 h64 as ⟨v53, s43, hinv43, h_v53⟩ growing hG carrying h_a0 h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v52 dropping he_v53 hinv42 e_v53 s42
  store_step with Store.apply_rep s43 v53 a0 _ _ hinv43 h64 h_v53 h_a0 (by ns_tac) (by ns_tac) as ⟨v54, s44, hinv44, h_v54⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v52 dropping h_a0 h_v53 hinv43 s43 v53
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s44 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv44 h64 as ⟨v55, s45, hinv45, h_v55⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v52 h_v54 dropping hinv44 s44
  store_step with Store.apply_rep s45 v54 v55 _ _ hinv45 h64 h_v54 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s46, hinv46, h_v56⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 h_v52 dropping h_v54 h_v55 hinv45 s45 v54 v55
  store_step with Store.apply_rep s46 v52 v56 _ _ hinv46 h64 h_v52 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s47, hinv47, h_v57⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 dropping h_v52 h_v56 hinv46 s46 v52 v56
  store_step with ih.eo__24eo_5ftypeof s47 v57 _ hinv47 h64 (hG.rem hrem) h_v57 as ⟨v58, s48, hinv48, h_v58⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 h_v45 h_v46 dropping h_v57 hinv47 s47 v57
  store_step with ih.eo__24eo_5fnil s48 v46 v58 _ _ hinv48 h64 (hG.rem hrem) h_v46 h_v58 as ⟨v59, s49, hinv49, h_v59⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 h_v45 dropping h_v46 h_v58 hinv48 s48 v46 v58
  store_step with Store.apply_mk_rep s49 v45 v59 _ _ hinv49 h64 h_v45 h_v59 as ⟨v60, s50, hinv50, h_v60⟩ growing hG carrying h_v17 h_v18 h_v19 h_v32 dropping h_v45 h_v59 hinv49 s49 v45 v59
  store_step with Store.apply_mk_rep s50 v32 v60 _ _ hinv50 h64 h_v32 h_v60 as ⟨v61, s51, hinv51, h_v61⟩ growing hG carrying h_v17 h_v18 h_v19 dropping h_v32 h_v60 hinv50 s50 v32 v60
  store_step with Store.apply_mk_rep s51 v19 v61 _ _ hinv51 h64 h_v19 h_v61 as ⟨v62, s52, hinv52, h_v62⟩ growing hG carrying h_v17 h_v18 dropping h_v19 h_v61 hinv51 s51 v19 v61
  store_step with Store.apply_mk_rep s52 v18 v62 _ _ hinv52 h64 h_v18 h_v62 as ⟨v63, s53, hinv53, h_v63⟩ growing hG carrying h_v17 dropping h_v18 h_v62 hinv52 s52 v18 v62
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s53 1#u32 (1) (by scalar_tac) hinv53 h64 as ⟨v64, s54, hinv54, h_v64⟩ growing hG carrying h_v17 h_v63 dropping hinv53 s53
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s54 e_v65 (by rw [he_v65]; rfl) h_v64 hinv54 h64 as ⟨v65, s55, hinv55, h_v65⟩ growing hG carrying h_v17 h_v63 dropping h_v64 he_v65 hinv54 e_v65 s54 v64
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s55 1#u32 (1) (by scalar_tac) hinv55 h64 as ⟨v66, s56, hinv56, h_v66⟩ growing hG carrying h_v17 h_v63 h_v65 dropping hinv55 s55
  store_step with Store.apply_rep s56 v65 v66 _ _ hinv56 h64 h_v65 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s57, hinv57, h_v67⟩ growing hG carrying h_v17 h_v63 dropping h_v65 h_v66 hinv56 s56 v65 v66
  store_step with Store.apply_mk_rep s57 v63 v67 _ _ hinv57 h64 h_v63 h_v67 as ⟨v68, s58, hinv58, h_v68⟩ growing hG carrying h_v17 dropping h_v63 h_v67 hinv57 s57 v63 v67
  store_step with Store.apply_mk_rep s58 v17 v68 _ _ hinv58 h64 h_v17 h_v68 as ⟨v69, s59, hinv59, h_v69⟩ growing hG carrying dropping h_v17 h_v68 hinv58 s58 v17 v68
  case_done hinv59 hG with h_v69 in EoCases.__eo_prog_bv_uaddo_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_bv_uaddo_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2duaddo_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_uaddo_eliminate x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_uaddo_eliminate.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_uaddo_eliminate
  unfold EoCases.__eo_prog_bv_uaddo_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_uaddo_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2duaddo_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_uaddo_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2duaddo_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2duaddo_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2duaddo_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_uaddo_eliminate x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2duaddo_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dudiv_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dudiv_2done s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_udiv_one.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_udiv_one.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dudiv_2done
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvudiv.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_a1 he_v3 hinv3 e_v3 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 1#u32 (1) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v2 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v2 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 dropping h_v0 h_v6 hinv7 s7 v0 v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_a0 h_v7 hinv8 s8 v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_udiv_one.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_udiv_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dudiv_2done.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_udiv_one x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_udiv_one.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_udiv_one
  unfold EoCases.__eo_prog_bv_udiv_one.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dudiv_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dudiv_2done s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_one x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dudiv_2done.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dudiv_2done
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dudiv_2done_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_udiv_one.case_0

theorem eo__24eo_5fprog_5fbv_2dudiv_2done_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dudiv_2done.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dudiv_2done
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dudiv_2done s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_udiv_one x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dudiv_2done_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_int_2eispow2.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_a8 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v15, x_v15, h_v15⟩ else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v15 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v18 h_v20 h_v21 dropping h_a6 h_v13 h_v15 h_v17 h_v4 he_v22 hinv3 e_v22 s3 v13 v15 v17 v4
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3e.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v18 h_v25 h_v27 h_v28 dropping h_v20 h_v21 h_v22 h_v24 he_v29 hinv4 e_v29 s4 v20 v21 v22 v24
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v28 a1 with h_v28 h_a1 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s5 1#u32 (1) (by scalar_tac) hinv5 h64 as ⟨v30, s6, hinv6, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v18 h_v25 dropping h_v27 h_v28 h_v29 hinv5 s5 v27 v28 v29
  pat_same v25 v30 with h_v25 h_v30 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  store_step with Store.literal_boolean_spec s6 true hinv6 h64 as ⟨v31, s7, hinv7, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_a8 h_v18 dropping h_v25 h_v30 hinv6 s6 v25 v30
  pat_same v18 v31 with h_v18 h_v31 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v33, x_v33, h_v33⟩ else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v33 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v40 (by rw [he_v40]; exact empty_args) hinv7 h64 as ⟨v40, s8, hinv8, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v36 h_v38 h_v39 dropping h_a7 h_v18 h_v31 h_v33 h_v35 he_v40 hinv7 e_v40 s7 v18 v31 v33 v35
  pat_same v38 v40 with h_v38 h_v40 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v39 a3 with h_v39 h_a3 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v36 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_int_2elog2.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a8 h_v42 h_v43 dropping h_v36 h_v38 h_v39 h_v40 he_v44 hinv8 e_v44 s8 v36 v38 v39 v40
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v43 a1 with h_v43 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a8 as ⟨v46, x_v46, h_v46⟩ else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v46 as ⟨v48, v49, x_v48, x_v49, h_v48, h_v49, hn_v48, hn_v49⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v48 as ⟨v51, v52, x_v51, x_v52, h_v51, h_v52, hn_v51, hn_v52⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v53 (by rw [he_v53]; exact empty_args) hinv9 h64 as ⟨v53, s10, hinv10, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v49 h_v51 h_v52 dropping h_a8 h_v42 h_v43 h_v44 h_v46 h_v48 he_v53 hinv9 e_v53 s9 v42 v43 v44 v46 v48
  pat_same v51 v53 with h_v51 h_v53 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v52 a4 with h_v52 h_a4 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v49 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_unapply h_v55 as ⟨v58, v59, x_v58, x_v59, h_v58, h_v59, hn_v58, hn_v59⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v60 (by rw [he_v60]; exact empty_args) hinv10 h64 as ⟨v60, s11, hinv11, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v56 h_v58 h_v59 dropping h_v49 h_v51 h_v52 h_v53 h_v55 he_v60 hinv10 e_v60 s10 v49 v51 v52 v53 v55
  pat_same v58 v60 with h_v58 h_v60 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  pat_same v59 a2 with h_v59 h_a2 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 1#u32 (1) (by scalar_tac) hinv11 h64 as ⟨v61, s12, hinv12, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v56 dropping h_v58 h_v59 h_v60 hinv11 s11 v58 v59 v60
  pat_same v56 v61 with h_v56 h_v61 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v62 (by rw [he_v62]; exact empty_args) hinv12 h64 as ⟨v62, s13, hinv13, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v56 h_v61 he_v62 hinv12 e_v62 s12 v56 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_bvudiv.construct s13 e_v63 (by rw [he_v63]; exact empty_args) hinv13 h64 as ⟨v63, s14, hinv14, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v62 dropping he_v63 hinv13 e_v63 s13
  store_step with Store.apply_rep s14 v63 a0 _ _ hinv14 h64 h_v63 h_a0 (by ns_tac) (by ns_tac) as ⟨v64, s15, hinv15, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v62 dropping h_v63 hinv14 s14 v63
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s15 e_v65 (by rw [he_v65]; rfl) h_a2 hinv15 h64 as ⟨v65, s16, hinv16, h_v65⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v62 h_v64 dropping h_a2 he_v65 hinv15 e_v65 s15
  store_step with Store.apply_rep s16 v65 a1 _ _ hinv16 h64 h_v65 h_a1 (by ns_tac) (by ns_tac) as ⟨v66, s17, hinv17, h_v66⟩ growing hG carrying h_a0 h_a3 h_a4 h_v62 h_v64 dropping h_a1 h_v65 hinv16 s16 v65
  store_step with Store.apply_rep s17 v64 v66 _ _ hinv17 h64 h_v64 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s18, hinv18, h_v67⟩ growing hG carrying h_a0 h_a3 h_a4 h_v62 dropping h_v64 h_v66 hinv17 s17 v64 v66
  store_step with Store.apply_rep s18 v62 v67 _ _ hinv18 h64 h_v62 h_v67 (by ns_tac) (by ns_tac) as ⟨v68, s19, hinv19, h_v68⟩ growing hG carrying h_a0 h_a3 h_a4 dropping h_v62 h_v67 hinv18 s18 v62 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_concat.construct s19 e_v69 (by rw [he_v69]; exact empty_args) hinv19 h64 as ⟨v69, s20, hinv20, h_v69⟩ growing hG carrying h_a0 h_a3 h_a4 h_v68 dropping he_v69 hinv19 e_v69 s19
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s20 e_v70 (by rw [he_v70]; rfl) h_a3 hinv20 h64 as ⟨v70, s21, hinv21, h_v70⟩ growing hG carrying h_a0 h_a3 h_a4 h_v68 h_v69 dropping he_v70 hinv20 e_v70 s20
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s21 0#u32 (0) (by scalar_tac) hinv21 h64 as ⟨v71, s22, hinv22, h_v71⟩ growing hG carrying h_a0 h_a3 h_a4 h_v68 h_v69 h_v70 dropping hinv21 s21
  store_step with Store.apply_rep s22 v70 v71 _ _ hinv22 h64 h_v70 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s23, hinv23, h_v72⟩ growing hG carrying h_a0 h_a3 h_a4 h_v68 h_v69 dropping h_v70 h_v71 hinv22 s22 v70 v71
  store_step with Store.apply_rep s23 v69 v72 _ _ hinv23 h64 h_v69 h_v72 (by ns_tac) (by ns_tac) as ⟨v73, s24, hinv24, h_v73⟩ growing hG carrying h_a0 h_a3 h_a4 h_v68 dropping h_v69 h_v72 hinv23 s23 v69 v72
  step as ⟨e_v74, he_v74⟩
  store_step with CtorSpec.eo_concat.construct s24 e_v74 (by rw [he_v74]; exact empty_args) hinv24 h64 as ⟨v74, s25, hinv25, h_v74⟩ growing hG carrying h_a0 h_a3 h_a4 h_v68 h_v73 dropping he_v74 hinv24 e_v74 s24
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_extract.construct s25 e_v75 (by rw [he_v75]; rfl) h_a4 h_a3 hinv25 h64 as ⟨v75, s26, hinv26, h_v75⟩ growing hG carrying h_a0 h_v68 h_v73 h_v74 dropping h_a3 h_a4 he_v75 hinv25 e_v75 s25
  store_step with Store.apply_rep s26 v75 a0 _ _ hinv26 h64 h_v75 h_a0 (by ns_tac) (by ns_tac) as ⟨v76, s27, hinv27, h_v76⟩ growing hG carrying h_v68 h_v73 h_v74 dropping h_a0 h_v75 hinv26 s26 v75
  store_step with Store.apply_rep s27 v74 v76 _ _ hinv27 h64 h_v74 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s28, hinv28, h_v77⟩ growing hG carrying h_v68 h_v73 dropping h_v74 h_v76 hinv27 s27 v74 v76
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s28 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv28 h64 as ⟨v78, s29, hinv29, h_v78⟩ growing hG carrying h_v68 h_v73 h_v77 dropping hinv28 s28
  store_step with Store.apply_rep s29 v77 v78 _ _ hinv29 h64 h_v77 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s30, hinv30, h_v79⟩ growing hG carrying h_v68 h_v73 dropping h_v77 h_v78 hinv29 s29 v77 v78
  store_step with Store.apply_rep s30 v73 v79 _ _ hinv30 h64 h_v73 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s31, hinv31, h_v80⟩ growing hG carrying h_v68 dropping h_v73 h_v79 hinv30 s30 v73 v79
  store_step with Store.apply_rep s31 v68 v80 _ _ hinv31 h64 h_v68 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s32, hinv32, h_v81⟩ growing hG carrying dropping h_v68 h_v80 hinv31 s31 v68 v80
  case_done hinv32 hG with h_v81 in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v17 hn_v18 hn_v20 hn_v21 hn_v24 hn_v25 hn_v27 hn_v28 hn_v35 hn_v36 hn_v38 hn_v39 hn_v42 hn_v43 hn_v48 hn_v49 hn_v51 hn_v52 hn_v55 hn_v56 hn_v58 hn_v59

/-- logos's `__eo_prog_bv_udiv_pow2_not_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) (hw_a8 : Valid.valid x_a8) :
    __eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_udiv_pow2_not_one
  unfold EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (x_a8 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (h_a8 : Represents.rep s a8 x_a8) :
    body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s a0 a1 a2 a3 a4 a5 a6 a7 a8 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7) (by valid_tac hinv h_a8)]
  unfold body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_udiv_pow2_not_one.case_0

theorem eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_a8
  unfold eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done s1 a0 a1 a2 a3 a4 a5 a6 a7 a8) (fun s' t => Represents.rep s' t (__eo_prog_bv_udiv_pow2_not_one x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 a8 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 x_a8 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn) (by congr_one h_a8 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_udiv_zero.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_udiv_zero.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvudiv.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a1 h_v0 h_v2 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 h_v0 h_v2 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a1 h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a1 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_bvnot.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a1 h_v7 dropping he_v8 hinv8 e_v8 s8
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s9 e_v9 (by rw [he_v9]; rfl) h_a1 hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v7 h_v8 dropping h_a1 he_v9 hinv9 e_v9 s9
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v7 h_v8 h_v9 dropping hinv10 s10
  store_step with Store.apply_rep s11 v9 v10 _ _ hinv11 h64 h_v9 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v7 h_v8 dropping h_v10 h_v9 hinv11 s11 v10 v9
  store_step with Store.apply_rep s12 v8 v11 _ _ hinv12 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v7 dropping h_v11 h_v8 hinv12 s12 v11 v8
  store_step with Store.apply_rep s13 v7 v12 _ _ hinv13 h64 h_v7 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying dropping h_v12 h_v7 hinv13 s13 v12 v7
  case_done hinv14 hG with h_v13 in EoCases.__eo_prog_bv_udiv_zero.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_udiv_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dudiv_2dzero.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_udiv_zero x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_udiv_zero.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_udiv_zero
  unfold EoCases.__eo_prog_bv_udiv_zero.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dudiv_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_udiv_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dudiv_2dzero.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dudiv_2dzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_udiv_zero.case_0

theorem eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dudiv_2dzero.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dudiv_2dzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dudiv_2dzero s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_udiv_zero x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dudiv_2dzero_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_uge_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_uge_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvuge.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvule.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_a1 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v4 h_v7 hinv8 s8 v4 v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_uge_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_uge_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2duge_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_uge_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_uge_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_uge_eliminate
  unfold EoCases.__eo_prog_bv_uge_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2duge_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_uge_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2duge_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2duge_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_uge_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2duge_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2duge_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2duge_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2duge_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_uge_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2duge_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dugt_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dugt_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ugt_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ugt_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dugt_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvugt.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_bvult.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v4 dropping h_a1 h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_v4 dropping h_a0 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v4 v7 _ _ hinv8 h64 h_v4 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying dropping h_v4 h_v7 hinv8 s8 v4 v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_bv_ugt_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_ugt_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dugt_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_ugt_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ugt_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ugt_eliminate
  unfold EoCases.__eo_prog_bv_ugt_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dugt_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dugt_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ugt_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dugt_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dugt_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dugt_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ugt_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dugt_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dugt_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dugt_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dugt_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_ugt_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dugt_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dugt_2durem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dugt_2durem s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ugt_urem.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ugt_urem.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dugt_2durem
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ugt_urem.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v10 h_v11 h_v12 he_v13 hinv2 e_v13 s2 v10 v11 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_bvugt.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping he_v14 hinv3 e_v14 s3
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_bvurem.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 h_v14 dropping he_v15 hinv4 e_v15 s4
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 h_v14 dropping h_v15 hinv5 s5 v15
  store_step with Store.apply_rep s6 v16 a1 _ _ hinv6 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 h_v14 dropping h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v14 v17 _ _ hinv7 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping h_v14 h_v17 hinv7 s7 v14 v17
  store_step with Store.apply_rep s8 v18 a1 _ _ hinv8 h64 h_v18 h_a1 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v13 dropping h_v18 hinv8 s8 v18
  store_step with Store.apply_rep s9 v13 v19 _ _ hinv9 h64 h_v13 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v19 hinv9 s9 v13 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_and.construct s10 e_v21 (by rw [he_v21]; exact empty_args) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v20 dropping he_v21 hinv10 e_v21 s10
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v22 (by rw [he_v22]; exact empty_args) hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v20 h_v21 dropping he_v22 hinv11 e_v22 s11
  store_step with Store.apply_rep s12 v22 a1 _ _ hinv12 h64 h_v22 h_a1 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a2 h_v20 h_v21 dropping h_a1 h_v22 hinv12 s12 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s13 e_v24 (by rw [he_v24]; rfl) h_a2 hinv13 h64 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a2 h_v20 h_v21 h_v23 dropping he_v24 hinv13 e_v24 s13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a2 h_v20 h_v21 h_v23 h_v24 dropping hinv14 s14
  store_step with Store.apply_rep s15 v24 v25 _ _ hinv15 h64 h_v24 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_a2 h_v20 h_v21 h_v23 dropping h_v24 h_v25 hinv15 s15 v24 v25
  store_step with Store.apply_rep s16 v23 v26 _ _ hinv16 h64 h_v23 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a0 h_a2 h_v20 h_v21 dropping h_v23 h_v26 hinv16 s16 v23 v26
  store_step with Store.apply_rep s17 v21 v27 _ _ hinv17 h64 h_v21 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_a0 h_a2 h_v20 dropping h_v21 h_v27 hinv17 s17 v21 v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_and.construct s18 e_v29 (by rw [he_v29]; exact empty_args) hinv18 h64 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_a0 h_a2 h_v20 h_v28 dropping he_v29 hinv18 e_v29 s18
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_bvugt.construct s19 e_v30 (by rw [he_v30]; exact empty_args) hinv19 h64 as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying h_a0 h_a2 h_v20 h_v28 h_v29 dropping he_v30 hinv19 e_v30 s19
  store_step with Store.apply_rep s20 v30 a0 _ _ hinv20 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying h_a2 h_v20 h_v28 h_v29 dropping h_a0 h_v30 hinv20 s20 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s21 e_v32 (by rw [he_v32]; rfl) h_a2 hinv21 h64 as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying h_v20 h_v28 h_v29 h_v31 dropping h_a2 he_v32 hinv21 e_v32 s21
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s22 0#u32 (0) (by scalar_tac) hinv22 h64 as ⟨v33, s23, hinv23, h_v33⟩ growing hG carrying h_v20 h_v28 h_v29 h_v31 h_v32 dropping hinv22 s22
  store_step with Store.apply_rep s23 v32 v33 _ _ hinv23 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s24, hinv24, h_v34⟩ growing hG carrying h_v20 h_v28 h_v29 h_v31 dropping h_v32 h_v33 hinv23 s23 v32 v33
  store_step with Store.apply_rep s24 v31 v34 _ _ hinv24 h64 h_v31 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s25, hinv25, h_v35⟩ growing hG carrying h_v20 h_v28 h_v29 dropping h_v31 h_v34 hinv24 s24 v31 v34
  store_step with Store.apply_rep s25 v29 v35 _ _ hinv25 h64 h_v29 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s26, hinv26, h_v36⟩ growing hG carrying h_v20 h_v28 dropping h_v29 h_v35 hinv25 s25 v29 v35
  store_step with Store.literal_boolean_spec s26 true hinv26 h64 as ⟨v37, s27, hinv27, h_v37⟩ growing hG carrying h_v20 h_v28 h_v36 dropping hinv26 s26
  store_step with Store.apply_rep s27 v36 v37 _ _ hinv27 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s28, hinv28, h_v38⟩ growing hG carrying h_v20 h_v28 dropping h_v36 h_v37 hinv27 s27 v36 v37
  store_step with Store.apply_rep s28 v28 v38 _ _ hinv28 h64 h_v28 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s29, hinv29, h_v39⟩ growing hG carrying h_v20 dropping h_v28 h_v38 hinv28 s28 v28 v38
  store_step with Store.apply_rep s29 v20 v39 _ _ hinv29 h64 h_v20 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s30, hinv30, h_v40⟩ growing hG carrying dropping h_v20 h_v39 hinv29 s29 v20 v39
  case_done hinv30 hG with h_v40 in EoCases.__eo_prog_bv_ugt_urem.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_bv_ugt_urem` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dugt_2durem.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_ugt_urem x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ugt_urem.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ugt_urem
  unfold EoCases.__eo_prog_bv_ugt_urem.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dugt_2durem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dugt_2durem s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ugt_urem x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dugt_2durem.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dugt_2durem
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dugt_2durem_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_ugt_urem.case_0

theorem eo__24eo_5fprog_5fbv_2dugt_2durem_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dugt_2durem.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dugt_2durem
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dugt_2durem s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_ugt_urem x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dugt_2durem_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dule_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dule_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ule_eliminate.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ule_eliminate.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dule_2deliminate
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvule.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v3 hinv4 s4 v0 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v4 dropping he_v5 hinv5 e_v5 s5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_bvult.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v4 h_v5 dropping he_v6 hinv6 e_v6 s6
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v4 h_v5 dropping h_a1 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v7 a0 _ _ hinv8 h64 h_v7 h_a0 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_v4 h_v5 dropping h_a0 h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v5 v8 _ _ hinv9 h64 h_v5 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_v4 dropping h_v5 h_v8 hinv9 s9 v5 v8
  store_step with Store.apply_rep s10 v4 v9 _ _ hinv10 h64 h_v4 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_v4 h_v9 hinv10 s10 v4 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_bv_ule_eliminate.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_ule_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dule_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_ule_eliminate x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ule_eliminate.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ule_eliminate
  unfold EoCases.__eo_prog_bv_ule_eliminate.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dule_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dule_2deliminate s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_eliminate x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dule_2deliminate.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dule_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dule_2deliminate_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ule_eliminate.case_0

theorem eo__24eo_5fprog_5fbv_2dule_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dule_2deliminate.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dule_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dule_2deliminate s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_ule_eliminate x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dule_2deliminate_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dule_2dmax_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dule_2dmax s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ule_max.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ule_max.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dule_2dmax
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v10 h_v11 dropping h_v4 h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v4 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v14, x_v14, h_v14⟩ else hinv2 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v14 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v21 (by rw [he_v21]; exact empty_args) hinv2 h64 as ⟨v21, s3, hinv3, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 h_v20 dropping h_a4 h_v10 h_v11 h_v12 h_v14 h_v16 he_v21 hinv2 e_v21 s2 v10 v11 v12 v14 v16
  pat_same v19 v21 with h_v19 h_v21 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_same v20 a1 with h_v20 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v17 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v23 as ⟨v26, v27, x_v26, x_v27, h_v26, h_v27, hn_v26, hn_v27⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__2d.construct s3 e_v28 (by rw [he_v28]; exact empty_args) hinv3 h64 as ⟨v28, s4, hinv4, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v24 h_v26 h_v27 dropping h_v17 h_v19 h_v20 h_v21 h_v23 he_v28 hinv3 e_v28 s3 v17 v19 v20 v21 v23
  pat_same v26 v28 with h_v26 h_v28 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_int_2epow2.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v24 h_v30 h_v31 dropping h_v26 h_v27 h_v28 he_v32 hinv4 e_v32 s4 v26 v27 v28
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__40bvsize.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v24 h_v34 h_v35 dropping h_v30 h_v31 h_v32 he_v36 hinv5 e_v36 s5 v30 v31 v32
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_ule_max.case_0
  pat_same v35 a0 with h_v35 h_a0 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_ule_max.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v24 dropping h_v34 h_v35 h_v36 hinv6 s6 v34 v35 v36
  pat_same v24 v37 with h_v24 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_ule_max.case_0
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v38 (by rw [he_v38]; exact empty_args) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v24 h_v37 he_v38 hinv7 e_v38 s7 v24 v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_bvule.construct s8 e_v39 (by rw [he_v39]; exact empty_args) hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v38 dropping he_v39 hinv8 e_v39 s8
  store_step with Store.apply_rep s9 v39 a0 _ _ hinv9 h64 h_v39 h_a0 (by ns_tac) (by ns_tac) as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a1 h_a2 h_v38 dropping h_a0 h_v39 hinv9 s9 v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s10 e_v41 (by rw [he_v41]; rfl) h_a2 hinv10 h64 as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a1 h_v38 h_v40 dropping h_a2 he_v41 hinv10 e_v41 s10
  store_step with Store.apply_rep s11 v41 a1 _ _ hinv11 h64 h_v41 h_a1 (by ns_tac) (by ns_tac) as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_v38 h_v40 dropping h_a1 h_v41 hinv11 s11 v41
  store_step with Store.apply_rep s12 v40 v42 _ _ hinv12 h64 h_v40 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying h_v38 dropping h_v40 h_v42 hinv12 s12 v40 v42
  store_step with Store.apply_rep s13 v38 v43 _ _ hinv13 h64 h_v38 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s14, hinv14, h_v44⟩ growing hG carrying dropping h_v38 h_v43 hinv13 s13 v38 v43
  store_step with Store.literal_boolean_spec s14 true hinv14 h64 as ⟨v45, s15, hinv15, h_v45⟩ growing hG carrying h_v44 dropping hinv14 s14
  store_step with Store.apply_rep s15 v44 v45 _ _ hinv15 h64 h_v44 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s16, hinv16, h_v46⟩ growing hG carrying dropping h_v44 h_v45 hinv15 s15 v44 v45
  case_done hinv16 hG with h_v46 in EoCases.__eo_prog_bv_ule_max.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v16 hn_v17 hn_v19 hn_v20 hn_v23 hn_v24 hn_v26 hn_v27 hn_v30 hn_v31 hn_v34 hn_v35

/-- logos's `__eo_prog_bv_ule_max` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dule_2dmax.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_bv_ule_max x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ule_max.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ule_max
  unfold EoCases.__eo_prog_bv_ule_max.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dule_2dmax_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fbv_2dule_2dmax s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_max x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dule_2dmax.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fbv_2dule_2dmax
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dule_2dmax_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_ule_max.case_0

theorem eo__24eo_5fprog_5fbv_2dule_2dmax_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dule_2dmax.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fbv_2dule_2dmax
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dule_2dmax s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_bv_ule_max x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dule_2dmax_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dule_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dule_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ule_self.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ule_self.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dule_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvule.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying dropping h_v0 h_v3 hinv4 s4 v0 v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_v4 dropping hinv5 s5
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_v4 h_v5 hinv6 s6 v4 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_bv_ule_self.case_0 using hn_a0

/-- logos's `__eo_prog_bv_ule_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dule_2dself.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_bv_ule_self x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ule_self.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ule_self
  unfold EoCases.__eo_prog_bv_ule_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dule_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fbv_2dule_2dself s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_self x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dule_2dself.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fbv_2dule_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dule_2dself_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_bv_ule_self.case_0

theorem eo__24eo_5fprog_5fbv_2dule_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dule_2dself.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fbv_2dule_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dule_2dself s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_bv_ule_self x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dule_2dself_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dule_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dule_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ule_zero.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ule_zero.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dule_2dzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvule.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v3 (by rw [he_v3]; rfl) h_a1 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 dropping hinv4 s4
  store_step with Store.apply_rep s5 v3 v4 _ _ hinv5 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v3 h_v4 hinv5 s5 v3 v4
  store_step with Store.apply_rep s6 v2 v5 _ _ hinv6 h64 h_v2 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v5 hinv6 s6 v2 v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v6 hinv7 s7 v0 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v7 dropping he_v8 hinv8 e_v8 s8
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_v7 dropping h_a0 h_v8 hinv9 s9 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s10 e_v10 (by rw [he_v10]; rfl) h_a1 hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_v7 h_v9 dropping h_a1 he_v10 hinv10 e_v10 s10
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v7 h_v9 h_v10 dropping hinv11 s11
  store_step with Store.apply_rep s12 v10 v11 _ _ hinv12 h64 h_v10 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_v7 h_v9 dropping h_v10 h_v11 hinv12 s12 v10 v11
  store_step with Store.apply_rep s13 v9 v12 _ _ hinv13 h64 h_v9 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v7 dropping h_v12 h_v9 hinv13 s13 v12 v9
  store_step with Store.apply_rep s14 v7 v13 _ _ hinv14 h64 h_v7 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v7 hinv14 s14 v13 v7
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_bv_ule_zero.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_bv_ule_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dule_2dzero.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_bv_ule_zero x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ule_zero.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ule_zero
  unfold EoCases.__eo_prog_bv_ule_zero.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dule_2dzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fbv_2dule_2dzero s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ule_zero x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dule_2dzero.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fbv_2dule_2dzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dule_2dzero_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ule_zero.case_0

theorem eo__24eo_5fprog_5fbv_2dule_2dzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dule_2dzero.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fbv_2dule_2dzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dule_2dzero s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_bv_ule_zero x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dule_2dzero_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fbv_2dult_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dult_2done s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_ult_one.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_ult_one.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dult_2done
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_ult_one.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_ult_one.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_ult_one.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ult_one.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ult_one.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_ult_one.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ult_one.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_ult_one.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_ult_one.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_ult_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_ult_one.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v11 h_v20 hinv4 s4 v11 v20
  pat_same v4 v21 with h_v4 h_v21 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_ult_one.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 dropping h_v21 h_v4 he_v22 hinv5 e_v22 s5 v21 v4
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_bvult.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_v22 dropping he_v23 hinv6 e_v23 s6
  store_step with Store.apply_rep s7 v23 a0 _ _ hinv7 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_v22 dropping h_v23 hinv7 s7 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v25 (by rw [he_v25]; rfl) h_a1 hinv8 h64 as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_v22 h_v24 dropping he_v25 hinv8 e_v25 s8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 1#u32 (1) (by scalar_tac) hinv9 h64 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_v22 h_v24 h_v25 dropping hinv9 s9
  store_step with Store.apply_rep s10 v25 v26 _ _ hinv10 h64 h_v25 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_v22 h_v24 dropping h_v25 h_v26 hinv10 s10 v25 v26
  store_step with Store.apply_rep s11 v24 v27 _ _ hinv11 h64 h_v24 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_v22 dropping h_v24 h_v27 hinv11 s11 v24 v27
  store_step with Store.apply_rep s12 v22 v28 _ _ hinv12 h64 h_v22 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 dropping h_v22 h_v28 hinv12 s12 v22 v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3d.construct s13 e_v30 (by rw [he_v30]; exact empty_args) hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_v29 dropping he_v30 hinv13 e_v30 s13
  store_step with Store.apply_rep s14 v30 a0 _ _ hinv14 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a1 h_v29 dropping h_a0 h_v30 hinv14 s14 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s15 e_v32 (by rw [he_v32]; rfl) h_a1 hinv15 h64 as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_v29 h_v31 dropping h_a1 he_v32 hinv15 e_v32 s15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_v29 h_v31 h_v32 dropping hinv16 s16
  store_step with Store.apply_rep s17 v32 v33 _ _ hinv17 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_v29 h_v31 dropping h_v32 h_v33 hinv17 s17 v32 v33
  store_step with Store.apply_rep s18 v31 v34 _ _ hinv18 h64 h_v31 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_v29 dropping h_v31 h_v34 hinv18 s18 v31 v34
  store_step with Store.apply_rep s19 v29 v35 _ _ hinv19 h64 h_v29 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying dropping h_v29 h_v35 hinv19 s19 v29 v35
  case_done hinv20 hG with h_v36 in EoCases.__eo_prog_bv_ult_one.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_bv_ult_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dult_2done.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_bv_ult_one x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_ult_one.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_ult_one
  unfold EoCases.__eo_prog_bv_ult_one.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fbv_2dult_2done_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fbv_2dult_2done s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_ult_one x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dult_2done.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fbv_2dult_2done
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dult_2done_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_bv_ult_one.case_0

theorem eo__24eo_5fprog_5fbv_2dult_2done_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dult_2done.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fbv_2dult_2done
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dult_2done s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_bv_ult_one x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dult_2done_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
