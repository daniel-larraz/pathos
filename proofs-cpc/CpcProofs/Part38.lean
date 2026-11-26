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
theorem case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_bv_mult_pow2_2b.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_bv_mult_pow2_2b.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b more_6_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_int_2eispow2.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__2d.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v18 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_int_2epow2.construct s3 e_v23 (by rw [he_v23]; exact empty_args) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22
  pat_same v21 v23 with h_v21 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v22 a1 with h_v22 h_a1 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v15 a2 with h_v15 h_a2 using hinv4 else hinv4 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23
  pat_same v4 v24 with h_v4 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v26, x_v26, h_v26⟩ else hinv5 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v26 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v32 a3 with h_v32 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v29 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_int_2elog2.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v36 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__2d.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_int_2epow2.construct s8 e_v48 (by rw [he_v48]; exact empty_args) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47
  pat_same v46 v48 with h_v46 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v47 a1 with h_v47 h_a1 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v40 a2 with h_v40 h_a2 using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v50, x_v50, h_v50⟩ else hinv9 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v50 as ⟨v52, v53, x_v52, x_v53, h_v52, h_v53, hn_v52, hn_v53⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v52 as ⟨v55, v56, x_v55, x_v56, h_v55, h_v56, hn_v55, hn_v56⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v57, he_v57⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v57 (by rw [he_v57]; exact empty_args) hinv9 h64 as ⟨v57, s10, hinv10, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56
  pat_same v55 v57 with h_v55 h_v57 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v56 a4 with h_v56 h_a4 using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v53 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v59 as ⟨v62, v63, x_v62, x_v63, h_v62, h_v63, hn_v62, hn_v63⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v64, he_v64⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v64 (by rw [he_v64]; exact empty_args) hinv10 h64 as ⟨v64, s11, hinv11, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63
  pat_same v62 v64 with h_v62 h_v64 using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v63 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v66 as ⟨v69, v70, x_v69, x_v70, h_v69, h_v70, hn_v69, hn_v70⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo__2d.construct s11 e_v71 (by rw [he_v71]; exact empty_args) hinv11 h64 as ⟨v71, s12, hinv12, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70
  pat_same v69 v71 with h_v69 h_v71 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v70 a1 with h_v70 h_a1 using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v67 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v75, he_v75⟩
  store_step with CtorSpec.eo_int_2elog2.construct s12 e_v75 (by rw [he_v75]; exact empty_args) hinv12 h64 as ⟨v75, s13, hinv13, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74
  pat_same v73 v75 with h_v73 h_v75 using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v74 as ⟨v77, v78, x_v77, x_v78, h_v77, h_v78, hn_v77, hn_v78⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v77 as ⟨v80, v81, x_v80, x_v81, h_v80, h_v81, hn_v80, hn_v81⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__2d.construct s13 e_v82 (by rw [he_v82]; exact empty_args) hinv13 h64 as ⟨v82, s14, hinv14, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81
  pat_same v80 v82 with h_v80 h_v82 using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_unapply h_v81 as ⟨v84, v85, x_v84, x_v85, h_v84, h_v85, hn_v84, hn_v85⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v86, he_v86⟩
  store_step with CtorSpec.eo_int_2epow2.construct s14 e_v86 (by rw [he_v86]; exact empty_args) hinv14 h64 as ⟨v86, s15, hinv15, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85
  pat_same v84 v86 with h_v84 h_v86 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v85 a1 with h_v85 h_a1 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  pat_same v78 a2 with h_v78 h_a2 using hinv15 else hinv15 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v87, s16, hinv16, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86
  pat_same v60 v87 with h_v60 h_v87 using hinv16 else hinv16 hG in EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v88 (by rw [he_v88]; exact empty_args) hinv16 h64 as ⟨v88, s17, hinv17, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87
  step as ⟨e_v89, he_v89⟩
  store_step with CtorSpec.eo_bvmul.construct s17 e_v89 (by rw [he_v89]; exact empty_args) hinv17 h64 as ⟨v89, s18, hinv18, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88
  store_step with Store.apply_rep s18 v89 a0 _ _ hinv18 h64 h_v89 h_a0 (by ns_tac) (by ns_tac) as ⟨v90, s19, hinv19, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89
  step as ⟨e_v91, he_v91⟩
  store_step with CtorSpec.eo_bvmul.construct s19 e_v91 (by rw [he_v91]; exact empty_args) hinv19 h64 as ⟨v91, s20, hinv20, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s20 e_v92 (by rw [he_v92]; rfl) h_a1 hinv20 h64 as ⟨v92, s21, hinv21, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91
  store_step with Store.apply_rep s21 v92 a2 _ _ hinv21 h64 h_v92 h_a2 (by ns_tac) (by ns_tac) as ⟨v93, s22, hinv22, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92
  store_step with Store.apply_rep s22 v91 v93 _ _ hinv22 h64 h_v91 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s23, hinv23, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_bvmul.construct s23 e_v95 (by rw [he_v95]; exact empty_args) hinv23 h64 as ⟨v95, s24, hinv24, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94
  store_step with ih.eo__24eo_5ftypeof s24 a0 _ hinv24 h64 (hG.rem hrem) h_a0 as ⟨v96, s25, hinv25, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95
  store_step with ih.eo__24eo_5fnil s25 v95 v96 _ _ hinv25 h64 (hG.rem hrem) h_v95 h_v96 as ⟨v97, s26, hinv26, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96
  store_step with Store.apply_mk_rep s26 v94 v97 _ _ hinv26 h64 h_v94 h_v97 as ⟨v98, s27, hinv27, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97
  store_step with Store.apply_mk_rep s27 v90 v98 _ _ hinv27 h64 h_v90 h_v98 as ⟨v99, s28, hinv28, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98
  store_step with Store.apply_mk_rep s28 v88 v99 _ _ hinv28 h64 h_v88 h_v99 as ⟨v100, s29, hinv29, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99
  step as ⟨e_v101, he_v101⟩
  store_step with CtorSpec.eo_concat.construct s29 e_v101 (by rw [he_v101]; exact empty_args) hinv29 h64 as ⟨v101, s30, hinv30, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s30 0#u32 (0) (by scalar_tac) hinv30 h64 as ⟨v102, s31, hinv31, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo_extract.construct s31 e_v103 (by rw [he_v103]; rfl) h_a4 h_v102 hinv31 h64 as ⟨v103, s32, hinv32, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102
  step as ⟨e_v104, he_v104⟩
  store_step with CtorSpec.eo_bvneg.construct s32 e_v104 (by rw [he_v104]; exact empty_args) hinv32 h64 as ⟨v104, s33, hinv33, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103
  store_step with Store.apply_rep s33 v104 a0 _ _ hinv33 h64 h_v104 h_a0 (by ns_tac) (by ns_tac) as ⟨v105, s34, hinv34, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104
  store_step with Store.apply_rep s34 v103 v105 _ _ hinv34 h64 h_v103 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s35, hinv35, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105
  store_step with Store.apply_rep s35 v101 v106 _ _ hinv35 h64 h_v101 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s36, hinv36, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106
  step as ⟨e_v108, he_v108⟩
  store_step with CtorSpec.eo_concat.construct s36 e_v108 (by rw [he_v108]; exact empty_args) hinv36 h64 as ⟨v108, s37, hinv37, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107
  step as ⟨e_v109, he_v109⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s37 e_v109 (by rw [he_v109]; rfl) h_a3 hinv37 h64 as ⟨v109, s38, hinv38, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s38 0#u32 (0) (by scalar_tac) hinv38 h64 as ⟨v110, s39, hinv39, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109
  store_step with Store.apply_rep s39 v109 v110 _ _ hinv39 h64 h_v109 h_v110 (by ns_tac) (by ns_tac) as ⟨v111, s40, hinv40, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110
  store_step with Store.apply_rep s40 v108 v111 _ _ hinv40 h64 h_v108 h_v111 (by ns_tac) (by ns_tac) as ⟨v112, s41, hinv41, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s41 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv41 h64 as ⟨v113, s42, hinv42, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112
  store_step with Store.apply_rep s42 v112 v113 _ _ hinv42 h64 h_v112 h_v113 (by ns_tac) (by ns_tac) as ⟨v114, s43, hinv43, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113
  store_step with Store.apply_rep s43 v107 v114 _ _ hinv43 h64 h_v107 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s44, hinv44, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114
  store_step with Store.apply_mk_rep s44 v100 v115 _ _ hinv44 h64 h_v100 h_v115 as ⟨v116, s45, hinv45, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v19 h_v21 h_v22 h_v23 h_v24 h_v26 h_v28 h_v29 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 h_v39 h_v40 h_v42 h_v43 h_v44 h_v46 h_v47 h_v48 h_v50 h_v52 h_v53 h_v55 h_v56 h_v57 h_v59 h_v60 h_v62 h_v63 h_v64 h_v66 h_v67 h_v69 h_v70 h_v71 h_v73 h_v74 h_v75 h_v77 h_v78 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91 h_v92 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115
  case_done hinv45 hG with h_v116 in EoCases.__eo_prog_bv_mult_pow2_2b.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15 hn_v17 hn_v18 hn_v21 hn_v22 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v52 hn_v53 hn_v55 hn_v56 hn_v59 hn_v60 hn_v62 hn_v63 hn_v66 hn_v67 hn_v69 hn_v70 hn_v73 hn_v74 hn_v77 hn_v78 hn_v80 hn_v81 hn_v84 hn_v85

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_bv_mult_pow2_2b` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_bv_mult_pow2_2b x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_bv_mult_pow2_2b.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_bv_mult_pow2_2b
  unfold EoCases.__eo_prog_bv_mult_pow2_2b.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_bv_mult_pow2_2b x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_bv_mult_pow2_2b.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_bv_mult_pow2_2b x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
