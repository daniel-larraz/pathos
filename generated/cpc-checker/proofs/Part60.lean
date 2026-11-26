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

set_option maxHeartbeats 20000000 in
theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_combine4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_combine4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_3_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_4_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_5_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 more_6_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v32 a3 with h_v32 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33
  pat_same v29 v34 with h_v29 h_v34 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34
  pat_same v22 v35 with h_v22 h_v35 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v37, x_v37, h_v37⟩ else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v37 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3e_3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__2b.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57
  pat_same v56 v58 with h_v56 h_v58 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v57 a3 with h_v57 h_a3 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v54 as ⟨v60, v61, x_v60, x_v61, h_v60, h_v61, hn_v60, hn_v61⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v60 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__2b.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v64 a4 with h_v64 h_a4 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65
  pat_same v61 v66 with h_v61 h_v66 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v47 as ⟨v68, v69, x_v68, x_v69, h_v68, h_v69, hn_v68, hn_v69⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_str_2elen.construct s13 e_v70 (by rw [he_v70]; exact empty_args) hinv13 h64 as ⟨v70, s14, hinv14, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69
  pat_same v68 v70 with h_v68 h_v70 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v69 as ⟨v72, v73, x_v72, x_v73, h_v72, h_v73, hn_v72, hn_v73⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v72 as ⟨v75, v76, x_v75, x_v76, h_v75, h_v76, hn_v75, hn_v76⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v75 as ⟨v78, v79, x_v78, x_v79, h_v78, h_v79, hn_v78, hn_v79⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s14 e_v80 (by rw [he_v80]; exact empty_args) hinv14 h64 as ⟨v80, s15, hinv15, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79
  pat_same v78 v80 with h_v78 h_v80 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v79 a0 with h_v79 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v76 a1 with h_v76 h_a1 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v73 a2 with h_v73 h_a2 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v81, s16, hinv16, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80
  pat_same v40 v81 with h_v40 h_v81 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v82 (by rw [he_v82]; exact empty_args) hinv16 h64 as ⟨v82, s17, hinv17, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s17 e_v83 (by rw [he_v83]; exact empty_args) hinv17 h64 as ⟨v83, s18, hinv18, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s18 e_v84 (by rw [he_v84]; exact empty_args) hinv18 h64 as ⟨v84, s19, hinv19, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83
  store_step with Store.apply_rep s19 v84 a0 _ _ hinv19 h64 h_v84 h_a0 (by ns_tac) (by ns_tac) as ⟨v85, s20, hinv20, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84
  store_step with Store.apply_rep s20 v85 a1 _ _ hinv20 h64 h_v85 h_a1 (by ns_tac) (by ns_tac) as ⟨v86, s21, hinv21, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85
  store_step with Store.apply_rep s21 v86 a2 _ _ hinv21 h64 h_v86 h_a2 (by ns_tac) (by ns_tac) as ⟨v87, s22, hinv22, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86
  store_step with Store.apply_rep s22 v83 v87 _ _ hinv22 h64 h_v83 h_v87 (by ns_tac) (by ns_tac) as ⟨v88, s23, hinv23, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87
  store_step with Store.apply_rep s23 v88 a3 _ _ hinv23 h64 h_v88 h_a3 (by ns_tac) (by ns_tac) as ⟨v89, s24, hinv24, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88
  store_step with Store.apply_rep s24 v89 a4 _ _ hinv24 h64 h_v89 h_a4 (by ns_tac) (by ns_tac) as ⟨v90, s25, hinv25, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89
  store_step with Store.apply_rep s25 v82 v90 _ _ hinv25 h64 h_v82 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s26, hinv26, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s26 e_v92 (by rw [he_v92]; exact empty_args) hinv26 h64 as ⟨v92, s27, hinv27, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91
  store_step with Store.apply_rep s27 v92 a0 _ _ hinv27 h64 h_v92 h_a0 (by ns_tac) (by ns_tac) as ⟨v93, s28, hinv28, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo__2b.construct s28 e_v94 (by rw [he_v94]; exact empty_args) hinv28 h64 as ⟨v94, s29, hinv29, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93
  store_step with Store.apply_rep s29 v94 a1 _ _ hinv29 h64 h_v94 h_a1 (by ns_tac) (by ns_tac) as ⟨v95, s30, hinv30, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo__2b.construct s30 e_v96 (by rw [he_v96]; exact empty_args) hinv30 h64 as ⟨v96, s31, hinv31, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95
  store_step with Store.apply_rep s31 v96 a3 _ _ hinv31 h64 h_v96 h_a3 (by ns_tac) (by ns_tac) as ⟨v97, s32, hinv32, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v98, s33, hinv33, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97
  store_step with Store.apply_rep s33 v97 v98 _ _ hinv33 h64 h_v97 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s34, hinv34, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98
  store_step with Store.apply_rep s34 v95 v99 _ _ hinv34 h64 h_v95 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s35, hinv35, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99
  store_step with Store.apply_rep s35 v93 v100 _ _ hinv35 h64 h_v93 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s36, hinv36, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo__2d.construct s36 e_v102 (by rw [he_v102]; exact empty_args) hinv36 h64 as ⟨v102, s37, hinv37, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101
  store_step with Store.apply_rep s37 v102 a2 _ _ hinv37 h64 h_v102 h_a2 (by ns_tac) (by ns_tac) as ⟨v103, s38, hinv38, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102
  store_step with Store.apply_rep s38 v103 a3 _ _ hinv38 h64 h_v103 h_a3 (by ns_tac) (by ns_tac) as ⟨v104, s39, hinv39, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103
  store_step with Store.apply_rep s39 v101 v104 _ _ hinv39 h64 h_v101 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s40, hinv40, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104
  store_step with Store.apply_rep s40 v91 v105 _ _ hinv40 h64 h_v91 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s41, hinv41, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 h_v22 h_v24 h_v25 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v34 h_v35 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v49 h_v50 h_v51 h_v53 h_v54 h_v56 h_v57 h_v58 h_v60 h_v61 h_v63 h_v64 h_v65 h_v66 h_v68 h_v69 h_v70 h_v72 h_v73 h_v75 h_v76 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105
  case_done hinv41 hG with h_v106 in EoCases.__eo_prog_str_substr_combine4.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57 hn_v60 hn_v61 hn_v63 hn_v64 hn_v68 hn_v69 hn_v72 hn_v73 hn_v75 hn_v76 hn_v78 hn_v79

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_str_substr_combine4` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_str_substr_combine4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_combine4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_combine4
  unfold EoCases.__eo_prog_str_substr_combine4.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_combine4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_substr_combine4.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_str_substr_combine4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
