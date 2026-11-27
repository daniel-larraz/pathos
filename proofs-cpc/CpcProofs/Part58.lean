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

set_option maxHeartbeats 4000000 in
theorem case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_sdiv_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_sdiv_eliminate.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v13 h_v14 dropping h_v10 h_v4 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v4 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v21 (by rw [he_v21]; exact empty_args) hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v11 h_v20 he_v21 hinv4 e_v21 s4 v11 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_bvsdiv.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping he_v22 hinv5 e_v22 s5
  store_step with Store.apply_rep s6 v22 a0 _ _ hinv6 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v22 hinv6 s6 v22
  store_step with Store.apply_rep s7 v23 a1 _ _ hinv7 h64 h_v23 h_a1 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v23 hinv7 s7 v23
  store_step with Store.apply_rep s8 v21 v24 _ _ hinv8 h64 h_v21 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v21 h_v24 hinv8 s8 v21 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v26 (by rw [he_v26]; exact empty_args) hinv9 h64 as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping he_v26 hinv9 e_v26 s9
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_xor.construct s10 e_v27 (by rw [he_v27]; exact empty_args) hinv10 h64 as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping he_v27 hinv10 e_v27 s10
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v28 (by rw [he_v28]; exact empty_args) hinv11 h64 as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping he_v28 hinv11 e_v28 s11
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_extract.construct s12 e_v29 (by rw [he_v29]; rfl) h_a2 h_a2 hinv12 h64 as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping he_v29 hinv12 e_v29 s12
  store_step with Store.apply_rep s13 v29 a0 _ _ hinv13 h64 h_v29 h_a0 (by ns_tac) (by ns_tac) as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v28 dropping h_v29 hinv13 s13 v29
  store_step with Store.apply_rep s14 v28 v30 _ _ hinv14 h64 h_v28 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v28 h_v30 hinv14 s14 v28 v30
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 dropping hinv15 s15
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s16 e_v33 (by rw [he_v33]; rfl) h_v32 hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 dropping h_v32 he_v33 hinv16 e_v33 s16 v32
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s17 1#u32 (1) (by scalar_tac) hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 h_v33 dropping hinv17 s17
  store_step with Store.apply_rep s18 v33 v34 _ _ hinv18 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 h_v31 dropping h_v33 h_v34 hinv18 s18 v33 v34
  store_step with Store.apply_rep s19 v31 v35 _ _ hinv19 h64 h_v31 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v27 dropping h_v31 h_v35 hinv19 s19 v31 v35
  store_step with Store.apply_rep s20 v27 v36 _ _ hinv20 h64 h_v27 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v27 h_v36 hinv20 s20 v27 v36
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s21 e_v38 (by rw [he_v38]; exact empty_args) hinv21 h64 as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 dropping he_v38 hinv21 e_v38 s21
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_extract.construct s22 e_v39 (by rw [he_v39]; rfl) h_a2 h_a2 hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v38 dropping he_v39 hinv22 e_v39 s22
  store_step with Store.apply_rep s23 v39 a1 _ _ hinv23 h64 h_v39 h_a1 (by ns_tac) (by ns_tac) as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v38 dropping h_v39 hinv23 s23 v39
  store_step with Store.apply_rep s24 v38 v40 _ _ hinv24 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 dropping h_v38 h_v40 hinv24 s24 v38 v40
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 1#u32 (1) (by scalar_tac) hinv25 h64 as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 dropping hinv25 s25
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s26 e_v43 (by rw [he_v43]; rfl) h_v42 hinv26 h64 as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 dropping h_v42 he_v43 hinv26 e_v43 s26 v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s27 1#u32 (1) (by scalar_tac) hinv27 h64 as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 h_v43 dropping hinv27 s27
  store_step with Store.apply_rep s28 v43 v44 _ _ hinv28 h64 h_v43 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 h_v41 dropping h_v43 h_v44 hinv28 s28 v43 v44
  store_step with Store.apply_rep s29 v41 v45 _ _ hinv29 h64 h_v41 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 h_v37 dropping h_v41 h_v45 hinv29 s29 v41 v45
  store_step with Store.apply_rep s30 v37 v46 _ _ hinv30 h64 h_v37 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v26 dropping h_v37 h_v46 hinv30 s30 v37 v46
  store_step with Store.apply_rep s31 v26 v47 _ _ hinv31 h64 h_v26 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v26 h_v47 hinv31 s31 v26 v47
  step as ⟨e_v49, he_v49⟩
  store_step with CtorSpec.eo_bvneg.construct s32 e_v49 (by rw [he_v49]; exact empty_args) hinv32 h64 as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 dropping he_v49 hinv32 e_v49 s32
  step as ⟨e_v50, he_v50⟩
  store_step with CtorSpec.eo_bvudiv.construct s33 e_v50 (by rw [he_v50]; exact empty_args) hinv33 h64 as ⟨v50, s34, hinv34, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 dropping he_v50 hinv33 e_v50 s33
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo_ite.construct s34 e_v51 (by rw [he_v51]; exact empty_args) hinv34 h64 as ⟨v51, s35, hinv35, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping he_v51 hinv34 e_v51 s34
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__3d.construct s35 e_v52 (by rw [he_v52]; exact empty_args) hinv35 h64 as ⟨v52, s36, hinv36, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 dropping he_v52 hinv35 e_v52 s35
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_extract.construct s36 e_v53 (by rw [he_v53]; rfl) h_a2 h_a2 hinv36 h64 as ⟨v53, s37, hinv37, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v52 dropping he_v53 hinv36 e_v53 s36
  store_step with Store.apply_rep s37 v53 a0 _ _ hinv37 h64 h_v53 h_a0 (by ns_tac) (by ns_tac) as ⟨v54, s38, hinv38, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v52 dropping h_v53 hinv37 s37 v53
  store_step with Store.apply_rep s38 v52 v54 _ _ hinv38 h64 h_v52 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s39, hinv39, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 dropping h_v52 h_v54 hinv38 s38 v52 v54
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s39 1#u32 (1) (by scalar_tac) hinv39 h64 as ⟨v56, s40, hinv40, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 dropping hinv39 s39
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s40 e_v57 (by rw [he_v57]; rfl) h_v56 hinv40 h64 as ⟨v57, s41, hinv41, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 dropping h_v56 he_v57 hinv40 e_v57 s40 v56
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s41 1#u32 (1) (by scalar_tac) hinv41 h64 as ⟨v58, s42, hinv42, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 h_v57 dropping hinv41 s41
  store_step with Store.apply_rep s42 v57 v58 _ _ hinv42 h64 h_v57 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s43, hinv43, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 h_v55 dropping h_v57 h_v58 hinv42 s42 v57 v58
  store_step with Store.apply_rep s43 v55 v59 _ _ hinv43 h64 h_v55 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s44, hinv44, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v51 dropping h_v55 h_v59 hinv43 s43 v55 v59
  store_step with Store.apply_rep s44 v51 v60 _ _ hinv44 h64 h_v51 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s45, hinv45, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping h_v51 h_v60 hinv44 s44 v51 v60
  step as ⟨e_v62, he_v62⟩
  store_step with CtorSpec.eo_bvneg.construct s45 e_v62 (by rw [he_v62]; exact empty_args) hinv45 h64 as ⟨v62, s46, hinv46, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v61 dropping he_v62 hinv45 e_v62 s45
  store_step with Store.apply_rep s46 v62 a0 _ _ hinv46 h64 h_v62 h_a0 (by ns_tac) (by ns_tac) as ⟨v63, s47, hinv47, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 h_v61 dropping h_v62 hinv46 s46 v62
  store_step with Store.apply_rep s47 v61 v63 _ _ hinv47 h64 h_v61 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s48, hinv48, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping h_v61 h_v63 hinv47 s47 v61 v63
  store_step with Store.apply_rep s48 v64 a0 _ _ hinv48 h64 h_v64 h_a0 (by ns_tac) (by ns_tac) as ⟨v65, s49, hinv49, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v50 dropping h_v64 hinv48 s48 v64
  store_step with Store.apply_rep s49 v50 v65 _ _ hinv49 h64 h_v50 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s50, hinv50, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 dropping h_v50 h_v65 hinv49 s49 v50 v65
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo_ite.construct s50 e_v67 (by rw [he_v67]; exact empty_args) hinv50 h64 as ⟨v67, s51, hinv51, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping he_v67 hinv50 e_v67 s50
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s51 e_v68 (by rw [he_v68]; exact empty_args) hinv51 h64 as ⟨v68, s52, hinv52, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 dropping he_v68 hinv51 e_v68 s51
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_extract.construct s52 e_v69 (by rw [he_v69]; rfl) h_a2 h_a2 hinv52 h64 as ⟨v69, s53, hinv53, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v68 dropping he_v69 hinv52 e_v69 s52
  store_step with Store.apply_rep s53 v69 a1 _ _ hinv53 h64 h_v69 h_a1 (by ns_tac) (by ns_tac) as ⟨v70, s54, hinv54, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v68 dropping h_v69 hinv53 s53 v69
  store_step with Store.apply_rep s54 v68 v70 _ _ hinv54 h64 h_v68 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s55, hinv55, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 dropping h_v68 h_v70 hinv54 s54 v68 v70
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s55 1#u32 (1) (by scalar_tac) hinv55 h64 as ⟨v72, s56, hinv56, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 dropping hinv55 s55
  step as ⟨e_v73, he_v73⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s56 e_v73 (by rw [he_v73]; rfl) h_v72 hinv56 h64 as ⟨v73, s57, hinv57, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 dropping h_v72 he_v73 hinv56 e_v73 s56 v72
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s57 1#u32 (1) (by scalar_tac) hinv57 h64 as ⟨v74, s58, hinv58, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 h_v73 dropping hinv57 s57
  store_step with Store.apply_rep s58 v73 v74 _ _ hinv58 h64 h_v73 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s59, hinv59, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 h_v71 dropping h_v73 h_v74 hinv58 s58 v73 v74
  store_step with Store.apply_rep s59 v71 v75 _ _ hinv59 h64 h_v71 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s60, hinv60, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v67 dropping h_v71 h_v75 hinv59 s59 v71 v75
  store_step with Store.apply_rep s60 v67 v76 _ _ hinv60 h64 h_v67 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s61, hinv61, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping h_v67 h_v76 hinv60 s60 v67 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_bvneg.construct s61 e_v78 (by rw [he_v78]; exact empty_args) hinv61 h64 as ⟨v78, s62, hinv62, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v77 dropping he_v78 hinv61 e_v78 s61
  store_step with Store.apply_rep s62 v78 a1 _ _ hinv62 h64 h_v78 h_a1 (by ns_tac) (by ns_tac) as ⟨v79, s63, hinv63, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 h_v77 dropping h_v78 hinv62 s62 v78
  store_step with Store.apply_rep s63 v77 v79 _ _ hinv63 h64 h_v77 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s64, hinv64, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping h_v77 h_v79 hinv63 s63 v77 v79
  store_step with Store.apply_rep s64 v80 a1 _ _ hinv64 h64 h_v80 h_a1 (by ns_tac) (by ns_tac) as ⟨v81, s65, hinv65, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 h_v66 dropping h_v80 hinv64 s64 v80
  store_step with Store.apply_rep s65 v66 v81 _ _ hinv65 h64 h_v66 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s66, hinv66, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 h_v49 dropping h_v66 h_v81 hinv65 s65 v66 v81
  store_step with Store.apply_rep s66 v49 v82 _ _ hinv66 h64 h_v49 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s67, hinv67, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v48 dropping h_v49 h_v82 hinv66 s66 v49 v82
  store_step with Store.apply_rep s67 v48 v83 _ _ hinv67 h64 h_v48 h_v83 (by ns_tac) (by ns_tac) as ⟨v84, s68, hinv68, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 dropping h_v48 h_v83 hinv67 s67 v48 v83
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo_bvudiv.construct s68 e_v85 (by rw [he_v85]; exact empty_args) hinv68 h64 as ⟨v85, s69, hinv69, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 dropping he_v85 hinv68 e_v85 s68
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_ite.construct s69 e_v86 (by rw [he_v86]; exact empty_args) hinv69 h64 as ⟨v86, s70, hinv70, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 dropping he_v86 hinv69 e_v86 s69
  step as ⟨e_v87, he_v87⟩
  store_step with CtorSpec.eo__3d.construct s70 e_v87 (by rw [he_v87]; exact empty_args) hinv70 h64 as ⟨v87, s71, hinv71, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 dropping he_v87 hinv70 e_v87 s70
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo_extract.construct s71 e_v88 (by rw [he_v88]; rfl) h_a2 h_a2 hinv71 h64 as ⟨v88, s72, hinv72, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v87 dropping he_v88 hinv71 e_v88 s71
  store_step with Store.apply_rep s72 v88 a0 _ _ hinv72 h64 h_v88 h_a0 (by ns_tac) (by ns_tac) as ⟨v89, s73, hinv73, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v87 dropping h_v88 hinv72 s72 v88
  store_step with Store.apply_rep s73 v87 v89 _ _ hinv73 h64 h_v87 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s74, hinv74, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 dropping h_v87 h_v89 hinv73 s73 v87 v89
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s74 1#u32 (1) (by scalar_tac) hinv74 h64 as ⟨v91, s75, hinv75, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 dropping hinv74 s74
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s75 e_v92 (by rw [he_v92]; rfl) h_v91 hinv75 h64 as ⟨v92, s76, hinv76, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 dropping h_v91 he_v92 hinv75 e_v92 s75 v91
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s76 1#u32 (1) (by scalar_tac) hinv76 h64 as ⟨v93, s77, hinv77, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 h_v92 dropping hinv76 s76
  store_step with Store.apply_rep s77 v92 v93 _ _ hinv77 h64 h_v92 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s78, hinv78, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 h_v90 dropping h_v92 h_v93 hinv77 s77 v92 v93
  store_step with Store.apply_rep s78 v90 v94 _ _ hinv78 h64 h_v90 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s79, hinv79, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v86 dropping h_v90 h_v94 hinv78 s78 v90 v94
  store_step with Store.apply_rep s79 v86 v95 _ _ hinv79 h64 h_v86 h_v95 (by ns_tac) (by ns_tac) as ⟨v96, s80, hinv80, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 dropping h_v86 h_v95 hinv79 s79 v86 v95
  step as ⟨e_v97, he_v97⟩
  store_step with CtorSpec.eo_bvneg.construct s80 e_v97 (by rw [he_v97]; exact empty_args) hinv80 h64 as ⟨v97, s81, hinv81, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v96 dropping he_v97 hinv80 e_v97 s80
  store_step with Store.apply_rep s81 v97 a0 _ _ hinv81 h64 h_v97 h_a0 (by ns_tac) (by ns_tac) as ⟨v98, s82, hinv82, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 h_v96 dropping h_v97 hinv81 s81 v97
  store_step with Store.apply_rep s82 v96 v98 _ _ hinv82 h64 h_v96 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s83, hinv83, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_v25 h_v84 h_v85 dropping h_v96 h_v98 hinv82 s82 v96 v98
  store_step with Store.apply_rep s83 v99 a0 _ _ hinv83 h64 h_v99 h_a0 (by ns_tac) (by ns_tac) as ⟨v100, s84, hinv84, h_v100⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 h_v85 dropping h_a0 h_v99 hinv83 s83 v99
  store_step with Store.apply_rep s84 v85 v100 _ _ hinv84 h64 h_v85 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s85, hinv85, h_v101⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 dropping h_v100 h_v85 hinv84 s84 v100 v85
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo_ite.construct s85 e_v102 (by rw [he_v102]; exact empty_args) hinv85 h64 as ⟨v102, s86, hinv86, h_v102⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 h_v101 dropping he_v102 hinv85 e_v102 s85
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo__3d.construct s86 e_v103 (by rw [he_v103]; exact empty_args) hinv86 h64 as ⟨v103, s87, hinv87, h_v103⟩ growing hG carrying h_a1 h_a2 h_v25 h_v84 h_v101 h_v102 dropping he_v103 hinv86 e_v103 s86
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_extract.construct s87 e_v104 (by rw [he_v104]; rfl) h_a2 h_a2 hinv87 h64 as ⟨v104, s88, hinv88, h_v104⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v103 dropping h_a2 he_v104 hinv87 e_v104 s87
  store_step with Store.apply_rep s88 v104 a1 _ _ hinv88 h64 h_v104 h_a1 (by ns_tac) (by ns_tac) as ⟨v105, s89, hinv89, h_v105⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v103 dropping h_v104 hinv88 s88 v104
  store_step with Store.apply_rep s89 v103 v105 _ _ hinv89 h64 h_v103 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s90, hinv90, h_v106⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 dropping h_v103 h_v105 hinv89 s89 v103 v105
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s90 1#u32 (1) (by scalar_tac) hinv90 h64 as ⟨v107, s91, hinv91, h_v107⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 dropping hinv90 s90
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s91 e_v108 (by rw [he_v108]; rfl) h_v107 hinv91 h64 as ⟨v108, s92, hinv92, h_v108⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 dropping h_v107 he_v108 hinv91 e_v108 s91 v107
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s92 1#u32 (1) (by scalar_tac) hinv92 h64 as ⟨v109, s93, hinv93, h_v109⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 h_v108 dropping hinv92 s92
  store_step with Store.apply_rep s93 v108 v109 _ _ hinv93 h64 h_v108 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s94, hinv94, h_v110⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 h_v106 dropping h_v108 h_v109 hinv93 s93 v108 v109
  store_step with Store.apply_rep s94 v106 v110 _ _ hinv94 h64 h_v106 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s95, hinv95, h_v111⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v102 dropping h_v106 h_v110 hinv94 s94 v106 v110
  store_step with Store.apply_rep s95 v102 v111 _ _ hinv95 h64 h_v102 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s96, hinv96, h_v112⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 dropping h_v102 h_v111 hinv95 s95 v102 v111
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo_bvneg.construct s96 e_v113 (by rw [he_v113]; exact empty_args) hinv96 h64 as ⟨v113, s97, hinv97, h_v113⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v112 dropping he_v113 hinv96 e_v113 s96
  store_step with Store.apply_rep s97 v113 a1 _ _ hinv97 h64 h_v113 h_a1 (by ns_tac) (by ns_tac) as ⟨v114, s98, hinv98, h_v114⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 h_v112 dropping h_v113 hinv97 s97 v113
  store_step with Store.apply_rep s98 v112 v114 _ _ hinv98 h64 h_v112 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s99, hinv99, h_v115⟩ growing hG carrying h_a1 h_v25 h_v84 h_v101 dropping h_v112 h_v114 hinv98 s98 v112 v114
  store_step with Store.apply_rep s99 v115 a1 _ _ hinv99 h64 h_v115 h_a1 (by ns_tac) (by ns_tac) as ⟨v116, s100, hinv100, h_v116⟩ growing hG carrying h_v25 h_v84 h_v101 dropping h_a1 h_v115 hinv99 s99 v115
  store_step with Store.apply_rep s100 v101 v116 _ _ hinv100 h64 h_v101 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s101, hinv101, h_v117⟩ growing hG carrying h_v25 h_v84 dropping h_v101 h_v116 hinv100 s100 v101 v116
  store_step with Store.apply_rep s101 v84 v117 _ _ hinv101 h64 h_v84 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s102, hinv102, h_v118⟩ growing hG carrying h_v25 dropping h_v117 h_v84 hinv101 s101 v117 v84
  store_step with Store.apply_rep s102 v25 v118 _ _ hinv102 h64 h_v25 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s103, hinv103, h_v119⟩ growing hG carrying dropping h_v118 h_v25 hinv102 s102 v118 v25
  case_done hinv103 hG with h_v119 in EoCases.__eo_prog_bv_sdiv_eliminate.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_sdiv_eliminate` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dsdiv_2deliminate.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_bv_sdiv_eliminate x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_sdiv_eliminate.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_sdiv_eliminate
  unfold EoCases.__eo_prog_bv_sdiv_eliminate.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_sdiv_eliminate x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dsdiv_2deliminate.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_bv_sdiv_eliminate.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dsdiv_2deliminate.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fbv_2dsdiv_2deliminate
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_bv_sdiv_eliminate x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
