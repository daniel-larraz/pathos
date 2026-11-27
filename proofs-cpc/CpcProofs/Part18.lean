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

theorem case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_1_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_2_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim more_3_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_int_2epow2.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  pat_same v36 a0 with h_v36 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v38 (by rw [he_v38]; exact empty_args) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_sbv_5fto_5fint.construct s8 e_v39 (by rw [he_v39]; exact empty_args) hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s9 v39 a0 _ _ hinv9 h64 h_v39 h_a0 (by ns_tac) (by ns_tac) as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s10 v38 v40 _ _ hinv10 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_ite.construct s11 e_v42 (by rw [he_v42]; exact empty_args) hinv11 h64 as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v43 (by rw [he_v43]; exact empty_args) hinv12 h64 as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_extract.construct s13 e_v44 (by rw [he_v44]; rfl) h_a1 h_a1 hinv13 h64 as ⟨v44, s14, hinv14, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s14 v44 a0 _ _ hinv14 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s15, hinv15, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s15 v43 v45 _ _ hinv15 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s16, hinv16, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 1#u32 (1) (by scalar_tac) hinv16 h64 as ⟨v47, s17, hinv17, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s17 e_v48 (by rw [he_v48]; rfl) h_v47 hinv17 h64 as ⟨v48, s18, hinv18, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v49, s19, hinv19, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s19 v48 v49 _ _ hinv19 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s20, hinv20, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s20 v46 v50 _ _ hinv20 h64 h_v46 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s21, hinv21, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s21 v42 v51 _ _ hinv21 h64 h_v42 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s22, hinv22, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s22 e_v53 (by rw [he_v53]; exact empty_args) hinv22 h64 as ⟨v53, s23, hinv23, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_rep s23 v53 a0 _ _ hinv23 h64 h_v53 h_a0 (by ns_tac) (by ns_tac) as ⟨v54, s24, hinv24, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s24 v52 v54 _ _ hinv24 h64 h_v52 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s25, hinv25, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo__2d.construct s25 e_v56 (by rw [he_v56]; exact empty_args) hinv25 h64 as ⟨v56, s26, hinv26, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s26 e_v57 (by rw [he_v57]; exact empty_args) hinv26 h64 as ⟨v57, s27, hinv27, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.apply_rep s27 v57 a0 _ _ hinv27 h64 h_v57 h_a0 (by ns_tac) (by ns_tac) as ⟨v58, s28, hinv28, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  store_step with Store.apply_rep s28 v56 v58 _ _ hinv28 h64 h_v56 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s29, hinv29, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
  store_step with Store.apply_rep s29 v59 a2 _ _ hinv29 h64 h_v59 h_a2 (by ns_tac) (by ns_tac) as ⟨v60, s30, hinv30, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
  store_step with Store.apply_rep s30 v55 v60 _ _ hinv30 h64 h_v55 h_v60 (by ns_tac) (by ns_tac) as ⟨v61, s31, hinv31, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
  store_step with Store.apply_rep s31 v41 v61 _ _ hinv31 h64 h_v41 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s32, hinv32, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
  case_done hinv32 hG with h_v62 in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v35 hn_v36

/-- logos's `__eo_prog_uf_sbv_to_int_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_sbv_to_int_elim.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_sbv_to_int_elim
  unfold EoCases.__eo_prog_uf_sbv_to_int_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_sbv_to_int_elim.case_0

theorem eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_uf_sbv_to_int_elim x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dsbv_2dto_2dint_2delim_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_xor_elim1.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_xor_elim1.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fxor_5felim1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_xor_elim1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_xor.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_xor_elim1.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s2 v9 v7 _ _ hinv2 h64 h_v9 h_v7 (by ns_tac) (by ns_tac) as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_or.construct s3 e_v11 (by rw [he_v11]; exact empty_args) hinv3 h64 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s4 v11 v4 _ _ hinv4 h64 h_v11 h_v4 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s6 v12 v13 _ _ hinv6 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s7 v10 v14 _ _ hinv7 h64 h_v10 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv8 hG with h_v15 in EoCases.__eo_prog_xor_elim1.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_xor_elim1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fxor_5felim1.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_xor_elim1 x_a0 =
      (firstSome [EoCases.__eo_prog_xor_elim1.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_xor_elim1
  unfold EoCases.__eo_prog_xor_elim1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fxor_5felim1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fxor_5felim1 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_xor_elim1 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fxor_5felim1.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fxor_5felim1
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fxor_5felim1_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_xor_elim1.case_0

theorem eo__24eo_5fprog_5fxor_5felim1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fxor_5felim1.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fxor_5felim1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fxor_5felim1 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_xor_elim1 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fxor_5felim1_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_xor_elim2.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_xor_elim2.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fxor_5felim2 more_0_eo__24eo_5fprog_5fxor_5felim2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_xor_elim2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_xor_elim2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_xor.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_xor_elim2.case_0
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_or.construct s1 e_v9 (by rw [he_v9]; exact empty_args) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_not.construct s2 e_v10 (by rw [he_v10]; exact empty_args) hinv2 h64 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s3 v10 v7 _ _ hinv3 h64 h_v10 h_v7 (by ns_tac) (by ns_tac) as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s4 v9 v11 _ _ hinv4 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s5, hinv5, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s5 e_v13 (by rw [he_v13]; exact empty_args) hinv5 h64 as ⟨v13, s6, hinv6, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s6 e_v14 (by rw [he_v14]; exact empty_args) hinv6 h64 as ⟨v14, s7, hinv7, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s7 v14 v4 _ _ hinv7 h64 h_v14 h_v4 (by ns_tac) (by ns_tac) as ⟨v15, s8, hinv8, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s8 v13 v15 _ _ hinv8 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s9, hinv9, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.literal_boolean_spec s9 false hinv9 h64 as ⟨v17, s10, hinv10, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s10 v16 v17 _ _ hinv10 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s11, hinv11, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s11 v12 v18 _ _ hinv11 h64 h_v12 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s12, hinv12, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv12 hG with h_v19 in EoCases.__eo_prog_xor_elim2.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_xor_elim2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fxor_5felim2.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_xor_elim2 x_a0 =
      (firstSome [EoCases.__eo_prog_xor_elim2.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_xor_elim2
  unfold EoCases.__eo_prog_xor_elim2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fxor_5felim2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fxor_5felim2 s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_xor_elim2 x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fxor_5felim2.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fxor_5felim2
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fxor_5felim2_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_xor_elim2.case_0

theorem eo__24eo_5fprog_5fxor_5felim2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fxor_5felim2.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fxor_5felim2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fxor_5felim2 s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_xor_elim2 x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fxor_5felim2_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_assume_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eassume_5fpush.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_assume_check.case_0 using

theorem case_1_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_assume_check.case_1 using

/-- logos's `__eo_push_assume_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fassume_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_assume_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_assume_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_assume_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_assume_check
  unfold EoCases.__eo_push_assume_check.case_0 EoCases.__eo_push_assume_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fassume_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5fassume_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fassume_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5fassume_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_assume_check.case_0 EoCases.__eo_push_assume_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5fassume_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fassume_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5fassume_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fassume_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_assume_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fassume_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_input_assume_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eassume.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_input_assume_check.case_0 using

theorem case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_input_assume_check.case_1 using

/-- logos's `__eo_push_input_assume_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5finput_5fassume_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_input_assume_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_input_assume_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_input_assume_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_input_assume_check
  unfold EoCases.__eo_push_input_assume_check.case_0 EoCases.__eo_push_input_assume_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5finput_5fassume_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5finput_5fassume_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5finput_5fassume_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_input_assume_check.case_0 EoCases.__eo_push_input_assume_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5finput_5fassume_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5finput_5fassume_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5finput_5fassume_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5finput_5fassume_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_input_assume_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5finput_5fassume_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a1 : StateOK x_a1) :
    case_0_eo__24eo_5fpush_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fproven
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fis_5fbool_5ftype s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24eo_5fpush_5fproven_5fcheck s1 v0 a0 a1 _ _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a0 h_a1 (by good_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_push_proven.case_0 using

/-- logos's `__eo_push_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_push_proven x_a0 x_a1 =
      (firstSome [EoCases.__eo_push_proven.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_push_proven
  unfold EoCases.__eo_push_proven.case_0
  logos_eq

theorem body_eo__24eo_5fpush_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a1 : StateOK x_a1) :
    body_eo__24eo_5fpush_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fproven.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fpush_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fproven_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_push_proven.case_0 splitting x_a0 x_a1

theorem eo__24eo_5fpush_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fproven.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a1
  unfold eo__24eo_5fpush_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fproven s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_push_proven x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fproven_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a1))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_0_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s true hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_push_proven_check.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fso_2eproven.construct s1 e_v1 (by rw [he_v1]; rfl) h_a1 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__24emb_5fs_2econs.construct s2 e_v2 (by rw [he_v2]; rfl) h_v1 h_a2 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_push_proven_check.case_0 using

theorem case_1_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    case_1_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  case_done hinv1 hG with h_v0 in EoCases.__eo_push_proven_check.case_1 using

/-- logos's `__eo_push_proven_check` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fpush_5fproven_5fcheck.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_push_proven_check x_a0 x_a1 x_a2 =
      (firstSome [EoCases.__eo_push_proven_check.case_0 x_a0 x_a1 x_a2, EoCases.__eo_push_proven_check.case_1 x_a0 x_a1 x_a2] default) := by
  conv => lhs; unfold __eo_push_proven_check
  unfold EoCases.__eo_push_proven_check.case_0 EoCases.__eo_push_proven_check.case_1
  logos_eq

theorem body_eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hg_a2 : StateOK x_a2) :
    body_eo__24eo_5fpush_5fproven_5fcheck s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fpush_5fproven_5fcheck.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fpush_5fproven_5fcheck
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fpush_5fproven_5fcheck_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using
  case_step with case_1_eo__24eo_5fpush_5fproven_5fcheck_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hg_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_push_proven_check.case_0 EoCases.__eo_push_proven_check.case_1 splitting x_a0 x_a1 x_a2

theorem eo__24eo_5fpush_5fproven_5fcheck_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fpush_5fproven_5fcheck.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hg_a2
  unfold eo__24eo_5fpush_5fproven_5fcheck
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fpush_5fproven_5fcheck s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_push_proven_check x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fpush_5fproven_5fcheck_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) hg_a2))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_0 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_state_is_closed.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_state_is_closed.case_0
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4
  case_done hinv1 hG with h_v5 in EoCases.__eo_state_is_closed.case_0 using

theorem case_1_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_1 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_state_is_closed.case_1
  case_again hinv hG with h_v2 goods 1 in EoCases.__eo_state_is_closed.case_1 using

theorem case_2_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_2_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_2 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_state_is_closed.case_2
  store_step with Store.native_bool_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_state_is_closed.case_2 using

theorem case_3_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_3_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__eo_state_is_closed.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          EoCases.__eo_state_is_closed.case_3 x_a0 = some (__eo_state_is_closed y0)
      | core.result.Result.Ok none => EoCases.__eo_state_is_closed.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  store_step with Store.native_bool_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_state_is_closed.case_3 using

/-- logos's `__eo_state_is_closed` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fstate_5fis_5fclosed.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_state_is_closed x_a0 =
      (firstSome [EoCases.__eo_state_is_closed.case_0 x_a0, EoCases.__eo_state_is_closed.case_1 x_a0, EoCases.__eo_state_is_closed.case_2 x_a0, EoCases.__eo_state_is_closed.case_3 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_state_is_closed
  unfold EoCases.__eo_state_is_closed.case_0 EoCases.__eo_state_is_closed.case_1 EoCases.__eo_state_is_closed.case_2 EoCases.__eo_state_is_closed.case_3
  logos_eq

theorem step_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    step_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _), arr.val = [u0] ∧ Represents.rep s' u0 y0 ∧ StateOK y0 ∧
          __eo_state_is_closed x_a0 = __eo_state_is_closed y0
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fstate_5fis_5fclosed.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold step_eo__24eo_5fstate_5fis_5fclosed
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0
  round_step with case_0_eo__24eo_5fstate_5fis_5fclosed_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 hbud using
  round_step with case_1_eo__24eo_5fstate_5fis_5fclosed_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 hbud using hc0
  round_step with case_2_eo__24eo_5fstate_5fis_5fclosed_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 hbud using hc0 hc1
  round_step with case_3_eo__24eo_5fstate_5fis_5fclosed_spec n ih s4 a0 x_a0 hinv4 h64 (hG.rem hrem) h_a0 hg_a0
    as ⟨s5, hinv5, hc3⟩ growing hG carrying h_a0 hbud using hc0 hc1 hc2
  round_stuck hinv5 hG using hc0 hc1 hc2 hc3 in EoCases.__eo_state_is_closed.case_0 EoCases.__eo_state_is_closed.case_1 EoCases.__eo_state_is_closed.case_2 EoCases.__eo_state_is_closed.case_3 splitting x_a0

theorem body_eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 : Term) (s : Store) (x_a0 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → StateOK x_a0 →
      body_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_closed x_a0)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 s x_a0 le_rfl hinv hrem h_a0 hg_a0
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 s x_a0 hk hinv hrem h_a0 hg_a0
  unfold body_eo__24eo_5fstate_5fis_5fclosed body_eo__24eo_5fstate_5fis_5fclosed_loop
  step with step_eo__24eo_5fstate_5fis_5fclosed_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, hnext, hrep0, hgood0, heq⟩ := hr
      simp only
      have hlen : next.length = 1 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      have hrec := ihl s1.budget (by omega) b0 s1 y0 le_rfl hinv1 (hg1.rem hrem)  hrep0  hgood0
      unfold body_eo__24eo_5fstate_5fis_5fclosed at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24eo_5fstate_5fis_5fclosed_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fis_5fclosed.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fstate_5fis_5fclosed
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fstate_5fis_5fclosed s1 a0) (fun s' t => Represents.rep s' t (__eo_state_is_closed x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fstate_5fis_5fclosed_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_state_is_refutation.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_state_is_refutation.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fstate_5fis_5frefutation
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 (by good_tac) as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  store_step with ih.eo__24eo_5fstate_5fis_5fclosed s2 v1 _ hinv2 h64 (hG.rem hrem) h_v1 (by good_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_state_is_refutation.case_0 using

/-- logos's `__eo_state_is_refutation` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fstate_5fis_5frefutation.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_state_is_refutation x_a0 =
      (firstSome [EoCases.__eo_state_is_refutation.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_state_is_refutation
  unfold EoCases.__eo_state_is_refutation.case_0
  logos_eq

theorem body_eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fstate_5fis_5frefutation s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_state_is_refutation x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fstate_5fis_5frefutation.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fstate_5fis_5frefutation
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fstate_5fis_5frefutation_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_state_is_refutation.case_0 splitting x_a0

theorem eo__24eo_5fstate_5fis_5frefutation_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fis_5frefutation.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fstate_5fis_5frefutation
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fstate_5fis_5frefutation s1 a0) (fun s' t => Represents.rep s' t (__eo_state_is_refutation x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fstate_5fis_5frefutation_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

/-- `$eo_state_proven_nth`, by the proof written by hand. -/
theorem eo__24eo_5fstate_5fproven_5fnth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fstate_5fproven_5fnth.Spec n :=
  state_proven_nth_spec n (fun m hm => (ih m hm).eo__24eo_5fStateObj_5fproven)

end pathos_compiled_checker
