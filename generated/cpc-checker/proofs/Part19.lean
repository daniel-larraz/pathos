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

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a4 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 h_v23 h_v24 dropping h_a4 h_v16 h_v18 h_v20 h_v4 he_v25 hinv3 e_v25 s3 v16 v18 v20 v4
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo__3e_3d.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 h_v28 h_v30 h_v31 dropping h_v23 h_v24 h_v25 h_v27 he_v32 hinv4 e_v32 s4 v23 v24 v25 v27
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_str_2elen.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 h_v28 h_v34 h_v35 dropping h_v30 h_v31 h_v32 he_v36 hinv5 e_v36 s5 v30 v31 v32
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_same v35 a2 with h_v35 h_a2 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_unapply h_v28 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 h_v38 h_v39 dropping h_v28 h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v28 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  pat_same v39 a1 with h_v39 h_a1 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v21 dropping h_v38 h_v39 h_v40 hinv7 s7 v38 v39 v40
  pat_same v21 v41 with h_v21 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v42 (by rw [he_v42]; exact empty_args) hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v21 h_v41 he_v42 hinv8 e_v42 s8 v21 v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s9 e_v43 (by rw [he_v43]; exact empty_args) hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 dropping he_v43 hinv9 e_v43 s9
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s10 e_v44 (by rw [he_v44]; exact empty_args) hinv10 h64 as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 h_v43 dropping he_v44 hinv10 e_v44 s10
  store_step with Store.apply_rep s11 v44 a0 _ _ hinv11 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 h_v43 dropping h_v44 hinv11 s11 v44
  store_step with Store.apply_rep s12 v45 a2 _ _ hinv12 h64 h_v45 h_a2 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 h_v43 dropping h_v45 hinv12 s12 v45
  store_step with Store.apply_rep s13 v46 a0 _ _ hinv13 h64 h_v46 h_a0 (by ns_tac) (by ns_tac) as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 h_v43 dropping h_v46 hinv13 s13 v46
  store_step with Store.apply_rep s14 v43 v47 _ _ hinv14 h64 h_v43 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 dropping h_v43 h_v47 hinv14 s14 v43 v47
  store_step with Store.apply_rep s15 v48 a0 _ _ hinv15 h64 h_v48 h_a0 (by ns_tac) (by ns_tac) as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 dropping h_v48 hinv15 s15 v48
  store_step with Store.apply_rep s16 v49 a1 _ _ hinv16 h64 h_v49 h_a1 (by ns_tac) (by ns_tac) as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v42 dropping h_v49 hinv16 s16 v49
  store_step with Store.apply_rep s17 v42 v50 _ _ hinv17 h64 h_v42 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v42 h_v50 hinv17 s17 v42 v50
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s18 e_v52 (by rw [he_v52]; exact empty_args) hinv18 h64 as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v51 dropping he_v52 hinv18 e_v52 s18
  step as ⟨e_v53, he_v53⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s19 e_v53 (by rw [he_v53]; exact empty_args) hinv19 h64 as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v51 h_v52 dropping he_v53 hinv19 e_v53 s19
  store_step with Store.apply_rep s20 v53 a0 _ _ hinv20 h64 h_v53 h_a0 (by ns_tac) (by ns_tac) as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v51 h_v52 dropping h_v53 hinv20 s20 v53
  store_step with Store.apply_rep s21 v54 a2 _ _ hinv21 h64 h_v54 h_a2 (by ns_tac) (by ns_tac) as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_a1 h_v51 h_v52 dropping h_a2 h_v54 hinv21 s21 v54
  store_step with Store.apply_rep s22 v55 a1 _ _ hinv22 h64 h_v55 h_a1 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_a0 h_a1 h_v51 h_v52 dropping h_v55 hinv22 s22 v55
  store_step with Store.apply_rep s23 v52 v56 _ _ hinv23 h64 h_v52 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_a0 h_a1 h_v51 dropping h_v52 h_v56 hinv23 s23 v52 v56
  store_step with Store.apply_rep s24 v57 a0 _ _ hinv24 h64 h_v57 h_a0 (by ns_tac) (by ns_tac) as ⟨v58, s25, hinv25, h_v58⟩ growing hG carrying h_a1 h_v51 dropping h_a0 h_v57 hinv24 s24 v57
  store_step with Store.apply_rep s25 v58 a1 _ _ hinv25 h64 h_v58 h_a1 (by ns_tac) (by ns_tac) as ⟨v59, s26, hinv26, h_v59⟩ growing hG carrying h_v51 dropping h_a1 h_v58 hinv25 s25 v58
  store_step with Store.apply_rep s26 v51 v59 _ _ hinv26 h64 h_v51 h_v59 (by ns_tac) (by ns_tac) as ⟨v60, s27, hinv27, h_v60⟩ growing hG carrying dropping h_v51 h_v59 hinv26 s26 v51 v59
  case_done hinv27 hG with h_v60 in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v30 hn_v31 hn_v34 hn_v35 hn_v38 hn_v39

/-- logos's `__eo_prog_str_repl_repl_lookahead_id_simp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_repl_repl_lookahead_id_simp x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_lookahead_id_simp
  unfold EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_lookahead_id_simp x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_repl_repl_lookahead_id_simp.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_lookahead_id_simp x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dlookahead_2did_2dsimp_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 hinv5 s5 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 dropping he_v20 hinv6 e_v20 s6
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v21 a0 _ _ hinv8 h64 h_v21 h_a0 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 dropping h_v21 hinv8 s8 v21
  store_step with Store.apply_rep s9 v22 a2 _ _ hinv9 h64 h_v22 h_a2 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_v17 h_v19 dropping h_a2 h_v22 hinv9 s9 v22
  store_step with Store.apply_rep s10 v19 v23 _ _ hinv10 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_v17 dropping h_v19 h_v23 hinv10 s10 v19 v23
  store_step with Store.apply_rep s11 v24 a1 _ _ hinv11 h64 h_v24 h_a1 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_v17 dropping h_v24 hinv11 s11 v24
  store_step with Store.apply_rep s12 v17 v25 _ _ hinv12 h64 h_v17 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 dropping h_v17 h_v25 hinv12 s12 v17 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s13 e_v27 (by rw [he_v27]; exact empty_args) hinv13 h64 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_v26 dropping he_v27 hinv13 e_v27 s13
  store_step with Store.apply_rep s14 v27 a0 _ _ hinv14 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a1 h_v26 dropping h_a0 h_v27 hinv14 s14 v27
  store_step with Store.apply_rep s15 v28 a1 _ _ hinv15 h64 h_v28 h_a1 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a1 h_v26 dropping h_v28 hinv15 s15 v28
  store_step with Store.apply_rep s16 v29 a1 _ _ hinv16 h64 h_v29 h_a1 (by ns_tac) (by ns_tac) as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_v26 dropping h_a1 h_v29 hinv16 s16 v29
  store_step with Store.apply_rep s17 v26 v30 _ _ hinv17 h64 h_v26 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying dropping h_v26 h_v30 hinv17 s17 v26 v30
  case_done hinv18 hG with h_v31 in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_repl_repl_src_inv_no_ctn1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_repl_repl_src_inv_no_ctn1 x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_src_inv_no_ctn1
  unfold EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn1.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1 s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn1 x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn1_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 hinv5 s5 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 dropping he_v20 hinv6 e_v20 s6
  store_step with Store.apply_rep s7 v20 a1 _ _ hinv7 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 dropping h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v21 a0 _ _ hinv8 h64 h_v21 h_a0 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 h_v19 dropping h_v21 hinv8 s8 v21
  store_step with Store.apply_rep s9 v22 a2 _ _ hinv9 h64 h_v22 h_a2 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_v17 h_v19 dropping h_a2 h_v22 hinv9 s9 v22
  store_step with Store.apply_rep s10 v19 v23 _ _ hinv10 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_v17 dropping h_v19 h_v23 hinv10 s10 v19 v23
  store_step with Store.apply_rep s11 v24 a0 _ _ hinv11 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_v17 dropping h_v24 hinv11 s11 v24
  store_step with Store.apply_rep s12 v17 v25 _ _ hinv12 h64 h_v17 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a1 dropping h_v17 h_v25 hinv12 s12 v17 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s13 e_v27 (by rw [he_v27]; exact empty_args) hinv13 h64 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a1 h_v26 dropping he_v27 hinv13 e_v27 s13
  store_step with Store.apply_rep s14 v27 a0 _ _ hinv14 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a1 h_v26 dropping h_v27 hinv14 s14 v27
  store_step with Store.apply_rep s15 v28 a1 _ _ hinv15 h64 h_v28 h_a1 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_v26 dropping h_a1 h_v28 hinv15 s15 v28
  store_step with Store.apply_rep s16 v29 a0 _ _ hinv16 h64 h_v29 h_a0 (by ns_tac) (by ns_tac) as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_v26 dropping h_a0 h_v29 hinv16 s16 v29
  store_step with Store.apply_rep s17 v26 v30 _ _ hinv17 h64 h_v26 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying dropping h_v26 h_v30 hinv17 s17 v26 v30
  case_done hinv18 hG with h_v31 in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_repl_repl_src_inv_no_ctn2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_repl_repl_src_inv_no_ctn2 x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_src_inv_no_ctn2
  unfold EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn2 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn2.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2 s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn2 x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn2_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v21 h_v23 h_v24 dropping h_a6 h_v16 h_v18 h_v20 h_v4 he_v25 hinv3 e_v25 s3 v16 v18 v20 v4
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v21 h_v28 h_v30 h_v31 dropping h_v23 h_v24 h_v25 h_v27 he_v32 hinv4 e_v32 s4 v23 v24 v25 v27
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_same v31 a0 with h_v31 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v21 dropping h_v28 h_v30 h_v31 h_v32 hinv5 s5 v28 v30 v31 v32
  pat_same v21 v33 with h_v21 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v21 h_v33 he_v34 hinv6 e_v34 s6 v21 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v34 dropping he_v35 hinv7 e_v35 s7
  store_step with Store.apply_rep s8 v35 a0 _ _ hinv8 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v34 dropping h_v35 hinv8 s8 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v34 h_v36 dropping he_v37 hinv9 e_v37 s9
  store_step with Store.apply_rep s10 v37 a1 _ _ hinv10 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v34 h_v36 dropping h_v37 hinv10 s10 v37
  store_step with Store.apply_rep s11 v38 a2 _ _ hinv11 h64 h_v38 h_a2 (by ns_tac) (by ns_tac) as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v34 h_v36 dropping h_a2 h_v38 hinv11 s11 v38
  store_step with Store.apply_rep s12 v39 a3 _ _ hinv12 h64 h_v39 h_a3 (by ns_tac) (by ns_tac) as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a0 h_a1 h_a4 h_v34 h_v36 dropping h_a3 h_v39 hinv12 s12 v39
  store_step with Store.apply_rep s13 v36 v40 _ _ hinv13 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_a0 h_a1 h_a4 h_v34 dropping h_v36 h_v40 hinv13 s13 v36 v40
  store_step with Store.apply_rep s14 v41 a4 _ _ hinv14 h64 h_v41 h_a4 (by ns_tac) (by ns_tac) as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying h_a0 h_a1 h_a4 h_v34 dropping h_v41 hinv14 s14 v41
  store_step with Store.apply_rep s15 v34 v42 _ _ hinv15 h64 h_v34 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_a0 h_a1 h_a4 dropping h_v34 h_v42 hinv15 s15 v34 v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s16 e_v44 (by rw [he_v44]; exact empty_args) hinv16 h64 as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying h_a0 h_a1 h_a4 h_v43 dropping he_v44 hinv16 e_v44 s16
  store_step with Store.apply_rep s17 v44 a0 _ _ hinv17 h64 h_v44 h_a0 (by ns_tac) (by ns_tac) as ⟨v45, s18, hinv18, h_v45⟩ growing hG carrying h_a1 h_a4 h_v43 dropping h_a0 h_v44 hinv17 s17 v44
  store_step with Store.apply_rep s18 v45 a1 _ _ hinv18 h64 h_v45 h_a1 (by ns_tac) (by ns_tac) as ⟨v46, s19, hinv19, h_v46⟩ growing hG carrying h_a4 h_v43 dropping h_a1 h_v45 hinv18 s18 v45
  store_step with Store.apply_rep s19 v46 a4 _ _ hinv19 h64 h_v46 h_a4 (by ns_tac) (by ns_tac) as ⟨v47, s20, hinv20, h_v47⟩ growing hG carrying h_v43 dropping h_a4 h_v46 hinv19 s19 v46
  store_step with Store.apply_rep s20 v43 v47 _ _ hinv20 h64 h_v43 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s21, hinv21, h_v48⟩ growing hG carrying dropping h_v43 h_v47 hinv20 s20 v43 v47
  case_done hinv21 hG with h_v48 in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v30 hn_v31

/-- logos's `__eo_prog_str_repl_repl_src_inv_no_ctn3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) :
    __eo_prog_str_repl_repl_src_inv_no_ctn3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_src_inv_no_ctn3
  unfold EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3 s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3_spec n ih s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_repl_repl_src_inv_no_ctn3.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3 s1 a0 a1 a2 a3 a4 a5 a6) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_src_inv_no_ctn3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dinv_2dno_2dctn3_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_src_self.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_src_self.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v2 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v0 h_v8 hinv9 s9 v0 v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v9 dropping he_v10 hinv10 e_v10 s10
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a2 h_v9 dropping h_a0 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v11 a1 _ _ hinv12 h64 h_v11 h_a1 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a2 h_v9 dropping h_a1 h_v11 hinv12 s12 v11
  store_step with Store.apply_rep s13 v12 a2 _ _ hinv13 h64 h_v12 h_a2 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_v9 dropping h_a2 h_v12 hinv13 s13 v12
  store_step with Store.apply_rep s14 v9 v13 _ _ hinv14 h64 h_v9 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying dropping h_v13 h_v9 hinv14 s14 v13 v9
  case_done hinv15 hG with h_v14 in EoCases.__eo_prog_str_repl_repl_src_self.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_str_repl_repl_src_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_repl_repl_src_self x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_src_self.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_src_self
  unfold EoCases.__eo_prog_str_repl_repl_src_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_self x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_repl_repl_src_self.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_src_self x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dself_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  pat_same v11 a3 with h_v11 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 dropping h_v18 hinv5 s5 v18
  store_step with Store.apply_rep s6 v19 a3 _ _ hinv6 h64 h_v19 h_a3 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 dropping h_v19 hinv6 s6 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s7 e_v21 (by rw [he_v21]; exact empty_args) hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 h_v20 dropping he_v21 hinv7 e_v21 s7
  store_step with Store.apply_rep s8 v21 a2 _ _ hinv8 h64 h_v21 h_a2 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 h_v20 dropping h_v21 hinv8 s8 v21
  store_step with Store.apply_rep s9 v22 a0 _ _ hinv9 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 h_v20 dropping h_v22 hinv9 s9 v22
  store_step with Store.apply_rep s10 v23 a1 _ _ hinv10 h64 h_v23 h_a1 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a2 h_a3 h_v17 h_v20 dropping h_a1 h_v23 hinv10 s10 v23
  store_step with Store.apply_rep s11 v20 v24 _ _ hinv11 h64 h_v20 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a2 h_a3 h_v17 dropping h_v20 h_v24 hinv11 s11 v20 v24
  store_step with Store.apply_rep s12 v17 v25 _ _ hinv12 h64 h_v17 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a2 h_a3 dropping h_v17 h_v25 hinv12 s12 v17 v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s13 e_v27 (by rw [he_v27]; exact empty_args) hinv13 h64 as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a2 h_a3 h_v26 dropping he_v27 hinv13 e_v27 s13
  store_step with Store.apply_rep s14 v27 a0 _ _ hinv14 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a2 h_a3 h_v26 dropping h_a0 h_v27 hinv14 s14 v27
  store_step with Store.apply_rep s15 v28 a3 _ _ hinv15 h64 h_v28 h_a3 (by ns_tac) (by ns_tac) as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a2 h_v26 dropping h_a3 h_v28 hinv15 s15 v28
  store_step with Store.apply_rep s16 v29 a2 _ _ hinv16 h64 h_v29 h_a2 (by ns_tac) (by ns_tac) as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_v26 dropping h_a2 h_v29 hinv16 s16 v29
  store_step with Store.apply_rep s17 v26 v30 _ _ hinv17 h64 h_v26 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying dropping h_v26 h_v30 hinv17 s17 v26 v30
  case_done hinv18 hG with h_v31 in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_repl_repl_src_tgt_no_ctn` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_repl_repl_src_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_src_tgt_no_ctn
  unfold EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_src_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_repl_repl_src_tgt_no_ctn.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_src_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dsrc_2dtgt_2dno_2dctn_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 dropping h_v18 hinv5 s5 v18
  store_step with Store.apply_rep s6 v19 a1 _ _ hinv6 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 dropping h_v19 hinv6 s6 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s7 e_v21 (by rw [he_v21]; exact empty_args) hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v17 h_v20 dropping he_v21 hinv7 e_v21 s7
  store_step with Store.apply_rep s8 v21 a1 _ _ hinv8 h64 h_v21 h_a1 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a2 h_a3 h_v17 h_v20 dropping h_a1 h_v21 hinv8 s8 v21
  store_step with Store.apply_rep s9 v22 a2 _ _ hinv9 h64 h_v22 h_a2 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a3 h_v17 h_v20 dropping h_a2 h_v22 hinv9 s9 v22
  store_step with Store.apply_rep s10 v23 a3 _ _ hinv10 h64 h_v23 h_a3 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_v17 h_v20 dropping h_a3 h_v23 hinv10 s10 v23
  store_step with Store.apply_rep s11 v20 v24 _ _ hinv11 h64 h_v20 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_v17 dropping h_v20 h_v24 hinv11 s11 v20 v24
  store_step with Store.apply_rep s12 v17 v25 _ _ hinv12 h64 h_v17 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 dropping h_v17 h_v25 hinv12 s12 v17 v25
  store_step with Store.apply_rep s13 v26 a0 _ _ hinv13 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying dropping h_a0 h_v26 hinv13 s13 v26
  case_done hinv14 hG with h_v27 in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_repl_repl_tgt_no_ctn` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_repl_repl_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_tgt_no_ctn
  unfold EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_repl_repl_tgt_no_ctn.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_tgt_no_ctn x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dno_2dctn_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_repl_repl_tgt_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_repl_repl_tgt_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v3 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v3 dropping h_a1 h_v6 hinv7 s7 v6
  store_step with Store.apply_rep s8 v3 v7 _ _ hinv8 h64 h_v3 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 dropping h_v3 h_v7 hinv8 s8 v3 v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 dropping h_v0 h_v8 hinv9 s9 v0 v8
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying dropping h_a0 h_v9 hinv10 s10 v9
  case_done hinv11 hG with h_v10 in EoCases.__eo_prog_str_repl_repl_tgt_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_repl_repl_tgt_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_repl_repl_tgt_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_repl_repl_tgt_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_repl_repl_tgt_self
  unfold EoCases.__eo_prog_str_repl_repl_tgt_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_repl_repl_tgt_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_repl_repl_tgt_self.case_0

theorem eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_repl_repl_tgt_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2drepl_2drepl_2dtgt_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_all_empty.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_all_empty.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_empty.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping he_v15 hinv4 e_v15 s4
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping h_v15 hinv5 s5 v15
  store_step with Store.apply_rep s6 v16 a1 _ _ hinv6 h64 h_v16 h_a1 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a2 h_v14 dropping h_a1 h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v17 a2 _ _ hinv7 h64 h_v17 h_a2 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v14 dropping h_a2 h_v17 hinv7 s7 v17
  store_step with Store.apply_rep s8 v14 v18 _ _ hinv8 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 dropping h_v14 h_v18 hinv8 s8 v14 v18
  store_step with Store.apply_rep s9 v19 a0 _ _ hinv9 h64 h_v19 h_a0 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying dropping h_a0 h_v19 hinv9 s9 v19
  case_done hinv10 hG with h_v20 in EoCases.__eo_prog_str_replace_all_empty.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_replace_all_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_replace_all_empty x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_all_empty.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_all_empty
  unfold EoCases.__eo_prog_str_replace_all_empty.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_empty x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_replace_all_empty.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_all_empty x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dempty_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_all_find_pre.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_all_find_pre.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s1 e_v18 (by rw [he_v18]; exact empty_args) hinv1 h64 as ⟨v18, s2, hinv2, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 h_v11 h_v14 h_v16 h_v17 dropping h_v10 h_v13 h_v6 h_v7 h_v8 he_v18 hinv1 e_v18 s1 v10 v13 v6 v7 v8
  pat_same v16 v18 with h_v16 h_v18 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v17 a0 with h_v17 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 h_v11 dropping h_v14 h_v16 h_v17 h_v18 hinv2 s2 v14 v16 v17 v18
  pat_same v11 v19 with h_v11 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_a6 h_v4 dropping h_v11 h_v19 hinv3 s3 v11 v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v27 h_v28 dropping h_a5 h_v20 h_v22 h_v24 h_v4 he_v29 hinv4 e_v29 s4 v20 v22 v24 v4
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3e.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v32 h_v34 h_v35 dropping h_v27 h_v28 h_v29 h_v31 he_v36 hinv5 e_v36 s5 v27 v28 v29 v31
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v35 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v32 h_v38 h_v39 dropping h_v34 h_v35 h_v36 he_v40 hinv6 e_v40 s6 v34 v35 v36
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v39 a1 with h_v39 h_a1 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s7 0#u32 (0) (by scalar_tac) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 h_v32 dropping h_v38 h_v39 h_v40 hinv7 s7 v38 v39 v40
  pat_same v32 v41 with h_v32 h_v41 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a6 h_v25 dropping h_v32 h_v41 hinv8 s8 v32 v41
  pat_same v25 v42 with h_v25 h_v42 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v44, x_v44, h_v44⟩ else hinv9 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v44 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v47 h_v49 h_v50 dropping h_a6 h_v25 h_v42 h_v44 h_v46 he_v51 hinv9 e_v51 s9 v25 v42 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v50 a3 with h_v50 h_a3 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v47 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v56 as ⟨v59, v60, x_v59, x_v60, h_v59, h_v60, hn_v59, hn_v60⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s10 e_v61 (by rw [he_v61]; exact empty_args) hinv10 h64 as ⟨v61, s11, hinv11, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v54 h_v57 h_v59 h_v60 dropping h_v47 h_v49 h_v50 h_v51 h_v53 h_v56 he_v61 hinv10 e_v61 s10 v47 v49 v50 v51 v53 v56
  pat_same v59 v61 with h_v59 h_v61 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v60 a0 with h_v60 h_a0 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v57 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_str_2elen.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v54 h_v63 h_v64 dropping h_v57 h_v59 h_v60 h_v61 he_v65 hinv11 e_v65 s11 v57 v59 v60 v61
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v64 a1 with h_v64 h_a1 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_unapply h_v54 as ⟨v67, v68, x_v67, x_v68, h_v67, h_v68, hn_v67, hn_v68⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_str_2elen.construct s12 e_v69 (by rw [he_v69]; exact empty_args) hinv12 h64 as ⟨v69, s13, hinv13, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v67 h_v68 dropping h_v54 h_v63 h_v64 h_v65 he_v69 hinv12 e_v69 s12 v54 v63 v64 v65
  pat_same v67 v69 with h_v67 h_v69 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  pat_same v68 a0 with h_v68 h_a0 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_all_find_pre.case_0
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo__3d.construct s13 e_v70 (by rw [he_v70]; exact empty_args) hinv13 h64 as ⟨v70, s14, hinv14, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v67 h_v68 h_v69 he_v70 hinv13 e_v70 s13 v67 v68 v69
  step as ⟨e_v71, he_v71⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s14 e_v71 (by rw [he_v71]; exact empty_args) hinv14 h64 as ⟨v71, s15, hinv15, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v70 dropping he_v71 hinv14 e_v71 s14
  store_step with Store.apply_rep s15 v71 a0 _ _ hinv15 h64 h_v71 h_a0 (by ns_tac) (by ns_tac) as ⟨v72, s16, hinv16, h_v72⟩ growing hG carrying h_a1 h_a2 h_a3 h_v70 dropping h_a0 h_v71 hinv15 s15 v71
  store_step with Store.apply_rep s16 v72 a1 _ _ hinv16 h64 h_v72 h_a1 (by ns_tac) (by ns_tac) as ⟨v73, s17, hinv17, h_v73⟩ growing hG carrying h_a1 h_a2 h_a3 h_v70 dropping h_v72 hinv16 s16 v72
  store_step with Store.apply_rep s17 v73 a2 _ _ hinv17 h64 h_v73 h_a2 (by ns_tac) (by ns_tac) as ⟨v74, s18, hinv18, h_v74⟩ growing hG carrying h_a1 h_a2 h_a3 h_v70 dropping h_v73 hinv17 s17 v73
  store_step with Store.apply_rep s18 v70 v74 _ _ hinv18 h64 h_v70 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s19, hinv19, h_v75⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_v70 h_v74 hinv18 s18 v70 v74
  step as ⟨e_v76, he_v76⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s19 e_v76 (by rw [he_v76]; exact empty_args) hinv19 h64 as ⟨v76, s20, hinv20, h_v76⟩ growing hG carrying h_a1 h_a2 h_a3 h_v75 dropping he_v76 hinv19 e_v76 s19
  store_step with Store.apply_rep s20 v76 a2 _ _ hinv20 h64 h_v76 h_a2 (by ns_tac) (by ns_tac) as ⟨v77, s21, hinv21, h_v77⟩ growing hG carrying h_a1 h_a2 h_a3 h_v75 dropping h_v76 hinv20 s20 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v78 (by rw [he_v78]; exact empty_args) hinv21 h64 as ⟨v78, s22, hinv22, h_v78⟩ growing hG carrying h_a1 h_a2 h_a3 h_v75 h_v77 dropping he_v78 hinv21 e_v78 s21
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s22 e_v79 (by rw [he_v79]; exact empty_args) hinv22 h64 as ⟨v79, s23, hinv23, h_v79⟩ growing hG carrying h_a1 h_a2 h_a3 h_v75 h_v77 h_v78 dropping he_v79 hinv22 e_v79 s22
  store_step with Store.apply_rep s23 v79 a3 _ _ hinv23 h64 h_v79 h_a3 (by ns_tac) (by ns_tac) as ⟨v80, s24, hinv24, h_v80⟩ growing hG carrying h_a1 h_a2 h_v75 h_v77 h_v78 dropping h_a3 h_v79 hinv23 s23 v79
  store_step with Store.apply_rep s24 v80 a1 _ _ hinv24 h64 h_v80 h_a1 (by ns_tac) (by ns_tac) as ⟨v81, s25, hinv25, h_v81⟩ growing hG carrying h_a2 h_v75 h_v77 h_v78 dropping h_a1 h_v80 hinv24 s24 v80
  store_step with Store.apply_rep s25 v81 a2 _ _ hinv25 h64 h_v81 h_a2 (by ns_tac) (by ns_tac) as ⟨v82, s26, hinv26, h_v82⟩ growing hG carrying h_a2 h_v75 h_v77 h_v78 dropping h_v81 hinv25 s25 v81
  store_step with Store.apply_rep s26 v78 v82 _ _ hinv26 h64 h_v78 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s27, hinv27, h_v83⟩ growing hG carrying h_a2 h_v75 h_v77 dropping h_v78 h_v82 hinv26 s26 v78 v82
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s27 e_v84 (by rw [he_v84]; exact empty_args) hinv27 h64 as ⟨v84, s28, hinv28, h_v84⟩ growing hG carrying h_a2 h_v75 h_v77 h_v83 dropping he_v84 hinv27 e_v84 s27
  store_step with ih.eo__24eo_5ftypeof s28 a2 _ hinv28 h64 (hG.rem hrem) h_a2 as ⟨v85, s29, hinv29, h_v85⟩ growing hG carrying h_v75 h_v77 h_v83 h_v84 dropping h_a2 hinv28 s28
  store_step with ih.eo__24eo_5fnil s29 v84 v85 _ _ hinv29 h64 (hG.rem hrem) h_v84 h_v85 as ⟨v86, s30, hinv30, h_v86⟩ growing hG carrying h_v75 h_v77 h_v83 dropping h_v84 h_v85 hinv29 s29 v84 v85
  store_step with Store.apply_mk_rep s30 v83 v86 _ _ hinv30 h64 h_v83 h_v86 as ⟨v87, s31, hinv31, h_v87⟩ growing hG carrying h_v75 h_v77 dropping h_v83 h_v86 hinv30 s30 v83 v86
  store_step with Store.apply_mk_rep s31 v77 v87 _ _ hinv31 h64 h_v77 h_v87 as ⟨v88, s32, hinv32, h_v88⟩ growing hG carrying h_v75 dropping h_v77 h_v87 hinv31 s31 v77 v87
  store_step with Store.apply_mk_rep s32 v75 v88 _ _ hinv32 h64 h_v75 h_v88 as ⟨v89, s33, hinv33, h_v89⟩ growing hG carrying dropping h_v75 h_v88 hinv32 s32 v75 v88
  case_done hinv33 hG with h_v89 in EoCases.__eo_prog_str_replace_all_find_pre.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v16 hn_v17 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57 hn_v59 hn_v60 hn_v63 hn_v64 hn_v67 hn_v68

/-- logos's `__eo_prog_str_replace_all_find_pre` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) :
    __eo_prog_str_replace_all_find_pre x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_all_find_pre.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_all_find_pre
  unfold EoCases.__eo_prog_str_replace_all_find_pre.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre s a0 a1 a2 a3 a4 a5 a6 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_find_pre x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre_spec n ih s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_replace_all_find_pre.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre s1 a0 a1 a2 a3 a4 a5 a6) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_all_find_pre x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dfind_2dpre_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_all_id.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_all_id.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 dropping h_a1 h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_a0 h_v5 hinv6 s6 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_str_replace_all_id.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_replace_all_id` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2did.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_replace_all_id x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_all_id.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_all_id
  unfold EoCases.__eo_prog_str_replace_all_id.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_id x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dall_2did.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_all_id.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2did_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dall_2did.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dall_2did
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_all_id x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2did_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_all_no_contains.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_all_no_contains.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_no_contains.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 hinv5 s5 v18
  store_step with Store.apply_rep s6 v19 a1 _ _ hinv6 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a2 h_v17 dropping h_a1 h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a2 _ _ hinv7 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_v17 dropping h_a2 h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v17 v21 _ _ hinv8 h64 h_v17 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 dropping h_v17 h_v21 hinv8 s8 v17 v21
  store_step with Store.apply_rep s9 v22 a0 _ _ hinv9 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying dropping h_a0 h_v22 hinv9 s9 v22
  case_done hinv10 hG with h_v23 in EoCases.__eo_prog_str_replace_all_no_contains.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_replace_all_no_contains` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_replace_all_no_contains x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_all_no_contains.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_all_no_contains
  unfold EoCases.__eo_prog_str_replace_all_no_contains.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_no_contains x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_replace_all_no_contains.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_all_no_contains x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dno_2dcontains_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_all_self.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_all_self.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_all_self.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_self.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_all_self.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_v4 h_v6 h_v7 dropping h_a2 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 h_v17 h_v18 dropping h_v13 h_v14 h_v15 he_v19 hinv2 e_v19 s2 v13 v14 v15
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  pat_same v18 a0 with h_v18 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v4 h_v11 dropping h_v17 h_v18 h_v19 hinv3 s3 v17 v18 v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  store_step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_v4 dropping h_v11 h_v20 hinv4 s4 v11 v20
  pat_same v4 v21 with h_v4 h_v21 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_all_self.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 dropping h_v21 h_v4 he_v22 hinv5 e_v22 s5 v21 v4
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_str_2ereplace_5fall.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_v22 dropping he_v23 hinv6 e_v23 s6
  store_step with Store.apply_rep s7 v23 a0 _ _ hinv7 h64 h_v23 h_a0 (by ns_tac) (by ns_tac) as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_v22 dropping h_v23 hinv7 s7 v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a1 h_v22 dropping h_a0 h_v24 hinv8 s8 v24
  store_step with Store.apply_rep s9 v25 a1 _ _ hinv9 h64 h_v25 h_a1 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a1 h_v22 dropping h_v25 hinv9 s9 v25
  store_step with Store.apply_rep s10 v22 v26 _ _ hinv10 h64 h_v22 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a1 dropping h_v22 h_v26 hinv10 s10 v22 v26
  store_step with Store.apply_rep s11 v27 a1 _ _ hinv11 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying dropping h_a1 h_v27 hinv11 s11 v27
  case_done hinv12 hG with h_v28 in EoCases.__eo_prog_str_replace_all_self.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_str_replace_all_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_replace_all_self x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_all_self.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_all_self
  unfold EoCases.__eo_prog_str_replace_all_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_all_self x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_all_self.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_all_self x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dall_2dself_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_dual_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_dual_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_same v11 a3 with h_v11 h_a3 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 h_v23 h_v24 dropping h_a5 h_v16 h_v18 h_v20 h_v4 he_v25 hinv3 e_v25 s3 v16 v18 v20 v4
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 h_v28 h_v30 h_v31 dropping h_v23 h_v24 h_v25 h_v27 he_v32 hinv4 e_v32 s4 v23 v24 v25 v27
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_same v31 a2 with h_v31 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 dropping h_v28 h_v30 h_v31 h_v32 hinv5 s5 v28 v30 v31 v32
  pat_same v21 v33 with h_v21 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_dual_ctn.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v21 h_v33 he_v34 hinv6 e_v34 s6 v21 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_str_2econtains.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping he_v35 hinv7 e_v35 s7
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s8 e_v36 (by rw [he_v36]; exact empty_args) hinv8 h64 as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 h_v35 dropping he_v36 hinv8 e_v36 s8
  store_step with Store.apply_rep s9 v36 a0 _ _ hinv9 h64 h_v36 h_a0 (by ns_tac) (by ns_tac) as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a1 h_a2 h_a3 h_v34 h_v35 dropping h_a0 h_v36 hinv9 s9 v36
  store_step with Store.apply_rep s10 v37 a1 _ _ hinv10 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a2 h_a3 h_v34 h_v35 dropping h_a1 h_v37 hinv10 s10 v37
  store_step with Store.apply_rep s11 v38 a2 _ _ hinv11 h64 h_v38 h_a2 (by ns_tac) (by ns_tac) as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a3 h_v34 h_v35 dropping h_a2 h_v38 hinv11 s11 v38
  store_step with Store.apply_rep s12 v35 v39 _ _ hinv12 h64 h_v35 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_a3 h_v34 dropping h_v35 h_v39 hinv12 s12 v35 v39
  store_step with Store.apply_rep s13 v40 a3 _ _ hinv13 h64 h_v40 h_a3 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_v34 dropping h_a3 h_v40 hinv13 s13 v40
  store_step with Store.apply_rep s14 v34 v41 _ _ hinv14 h64 h_v34 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying dropping h_v34 h_v41 hinv14 s14 v34 v41
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_v42 dropping hinv15 s15
  store_step with Store.apply_rep s16 v42 v43 _ _ hinv16 h64 h_v42 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying dropping h_v42 h_v43 hinv16 s16 v42 v43
  case_done hinv17 hG with h_v44 in EoCases.__eo_prog_str_replace_dual_ctn.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v30 hn_v31

/-- logos's `__eo_prog_str_replace_dual_ctn` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_replace_dual_ctn x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_dual_ctn.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_dual_ctn
  unfold EoCases.__eo_prog_str_replace_dual_ctn.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_dual_ctn x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_replace_dual_ctn.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_dual_ctn x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_dual_ctn_false.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_dual_ctn_false.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v18, x_v18, h_v18⟩ else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v18 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v25 (by rw [he_v25]; exact empty_args) hinv3 h64 as ⟨v25, s4, hinv4, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 h_v23 h_v24 dropping h_a5 h_v16 h_v18 h_v20 h_v4 he_v25 hinv3 e_v25 s3 v16 v18 v20 v4
  pat_same v23 v25 with h_v23 h_v25 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_unapply h_v27 as ⟨v30, v31, x_v30, x_v31, h_v30, h_v31, hn_v30, hn_v31⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v32 (by rw [he_v32]; exact empty_args) hinv4 h64 as ⟨v32, s5, hinv5, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 h_v28 h_v30 h_v31 dropping h_v23 h_v24 h_v25 h_v27 he_v32 hinv4 e_v32 s4 v23 v24 v25 v27
  pat_same v30 v32 with h_v30 h_v32 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_same v31 a0 with h_v31 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  pat_same v28 a3 with h_v28 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v21 dropping h_v28 h_v30 h_v31 h_v32 hinv5 s5 v28 v30 v31 v32
  pat_same v21 v33 with h_v21 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v34 (by rw [he_v34]; exact empty_args) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v21 h_v33 he_v34 hinv6 e_v34 s6 v21 v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_str_2econtains.construct s7 e_v35 (by rw [he_v35]; exact empty_args) hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v34 dropping he_v35 hinv7 e_v35 s7
  store_step with Store.apply_rep s8 v35 a0 _ _ hinv8 h64 h_v35 h_a0 (by ns_tac) (by ns_tac) as ⟨v36, s9, hinv9, h_v36⟩ growing hG carrying h_a1 h_a2 h_a3 h_v34 dropping h_a0 h_v35 hinv8 s8 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s9 e_v37 (by rw [he_v37]; exact empty_args) hinv9 h64 as ⟨v37, s10, hinv10, h_v37⟩ growing hG carrying h_a1 h_a2 h_a3 h_v34 h_v36 dropping he_v37 hinv9 e_v37 s9
  store_step with Store.apply_rep s10 v37 a1 _ _ hinv10 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s11, hinv11, h_v38⟩ growing hG carrying h_a2 h_a3 h_v34 h_v36 dropping h_a1 h_v37 hinv10 s10 v37
  store_step with Store.apply_rep s11 v38 a2 _ _ hinv11 h64 h_v38 h_a2 (by ns_tac) (by ns_tac) as ⟨v39, s12, hinv12, h_v39⟩ growing hG carrying h_a3 h_v34 h_v36 dropping h_a2 h_v38 hinv11 s11 v38
  store_step with Store.apply_rep s12 v39 a3 _ _ hinv12 h64 h_v39 h_a3 (by ns_tac) (by ns_tac) as ⟨v40, s13, hinv13, h_v40⟩ growing hG carrying h_v34 h_v36 dropping h_a3 h_v39 hinv12 s12 v39
  store_step with Store.apply_rep s13 v36 v40 _ _ hinv13 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s14, hinv14, h_v41⟩ growing hG carrying h_v34 dropping h_v36 h_v40 hinv13 s13 v36 v40
  store_step with Store.apply_rep s14 v34 v41 _ _ hinv14 h64 h_v34 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s15, hinv15, h_v42⟩ growing hG carrying dropping h_v34 h_v41 hinv14 s14 v34 v41
  store_step with Store.literal_boolean_spec s15 false hinv15 h64 as ⟨v43, s16, hinv16, h_v43⟩ growing hG carrying h_v42 dropping hinv15 s15
  store_step with Store.apply_rep s16 v42 v43 _ _ hinv16 h64 h_v42 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s17, hinv17, h_v44⟩ growing hG carrying dropping h_v42 h_v43 hinv16 s16 v42 v43
  case_done hinv17 hG with h_v44 in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v20 hn_v21 hn_v23 hn_v24 hn_v27 hn_v28 hn_v30 hn_v31

/-- logos's `__eo_prog_str_replace_dual_ctn_false` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_replace_dual_ctn_false x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_dual_ctn_false.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_dual_ctn_false
  unfold EoCases.__eo_prog_str_replace_dual_ctn_false.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_dual_ctn_false x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_replace_dual_ctn_false.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_dual_ctn_false x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2ddual_2dctn_2dfalse_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_emp_ctn_src.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_emp_ctn_src.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping he_v15 hinv4 e_v15 s4
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping h_v15 hinv5 s5 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v16 dropping he_v17 hinv6 e_v17 s6
  store_step with Store.apply_rep s7 v17 a2 _ _ hinv7 h64 h_v17 h_a2 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v16 dropping h_v17 hinv7 s7 v17
  store_step with Store.apply_rep s8 v18 a0 _ _ hinv8 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v16 dropping h_v18 hinv8 s8 v18
  store_step with Store.apply_rep s9 v19 a1 _ _ hinv9 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 h_v16 dropping h_v19 hinv9 s9 v19
  store_step with Store.apply_rep s10 v16 v20 _ _ hinv10 h64 h_v16 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping h_v16 h_v20 hinv10 s10 v16 v20
  store_step with Store.apply_rep s11 v14 v21 _ _ hinv11 h64 h_v14 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v14 h_v21 hinv11 s11 v14 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s12 e_v23 (by rw [he_v23]; exact empty_args) hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v22 dropping he_v23 hinv12 e_v23 s12
  store_step with Store.apply_rep s13 v23 a2 _ _ hinv13 h64 h_v23 h_a2 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v22 dropping h_v23 hinv13 s13 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s14 e_v25 (by rw [he_v25]; exact empty_args) hinv14 h64 as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v22 h_v24 dropping he_v25 hinv14 e_v25 s14
  store_step with Store.apply_rep s15 v25 a2 _ _ hinv15 h64 h_v25 h_a2 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_a1 h_v22 h_v24 dropping h_a2 h_v25 hinv15 s15 v25
  store_step with Store.apply_rep s16 v26 a0 _ _ hinv16 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a1 h_v22 h_v24 dropping h_a0 h_v26 hinv16 s16 v26
  store_step with Store.apply_rep s17 v27 a1 _ _ hinv17 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_v22 h_v24 dropping h_a1 h_v27 hinv17 s17 v27
  store_step with Store.apply_rep s18 v24 v28 _ _ hinv18 h64 h_v24 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_v22 dropping h_v24 h_v28 hinv18 s18 v24 v28
  store_step with Store.apply_rep s19 v22 v29 _ _ hinv19 h64 h_v22 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying dropping h_v22 h_v29 hinv19 s19 v22 v29
  case_done hinv20 hG with h_v30 in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_replace_emp_ctn_src` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_replace_emp_ctn_src x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_emp_ctn_src.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_emp_ctn_src
  unfold EoCases.__eo_prog_str_replace_emp_ctn_src.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_emp_ctn_src x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_replace_emp_ctn_src.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_emp_ctn_src x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2demp_2dctn_2dsrc_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dempty s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_empty.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_empty.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_empty.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_empty.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_empty.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_empty.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_empty.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v10 h_v11 dropping h_v6 h_v7 h_v8 he_v12 hinv1 e_v12 s1 v6 v7 v8
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_empty.case_0
  pat_same v11 a2 with h_v11 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_empty.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v10 h_v11 h_v12 hinv2 s2 v10 v11 v12
  pat_same v4 v13 with h_v4 h_v13 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_empty.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v13 h_v4 he_v14 hinv3 e_v14 s3 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping he_v15 hinv4 e_v15 s4
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v14 dropping h_v15 hinv5 s5 v15
  store_step with Store.apply_rep s6 v16 a2 _ _ hinv6 h64 h_v16 h_a2 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_v14 dropping h_a2 h_v16 hinv6 s6 v16
  store_step with Store.apply_rep s7 v17 a1 _ _ hinv7 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_v14 dropping h_v17 hinv7 s7 v17
  store_step with Store.apply_rep s8 v14 v18 _ _ hinv8 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 dropping h_v14 h_v18 hinv8 s8 v14 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s9 e_v20 (by rw [he_v20]; exact empty_args) hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_v19 dropping he_v20 hinv9 e_v20 s9
  store_step with Store.apply_rep s10 v20 a1 _ _ hinv10 h64 h_v20 h_a1 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_v19 dropping h_v20 hinv10 s10 v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s11 e_v22 (by rw [he_v22]; exact empty_args) hinv11 h64 as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_v19 h_v21 dropping he_v22 hinv11 e_v22 s11
  store_step with Store.apply_rep s12 v22 a0 _ _ hinv12 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a1 h_v19 h_v21 dropping h_a0 h_v22 hinv12 s12 v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s13 e_v24 (by rw [he_v24]; exact empty_args) hinv13 h64 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a1 h_v19 h_v21 h_v23 dropping he_v24 hinv13 e_v24 s13
  store_step with ih.eo__24eo_5ftypeof s14 a1 _ hinv14 h64 (hG.rem hrem) h_a1 as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_v19 h_v21 h_v23 h_v24 dropping h_a1 hinv14 s14
  store_step with ih.eo__24eo_5fnil s15 v24 v25 _ _ hinv15 h64 (hG.rem hrem) h_v24 h_v25 as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_v19 h_v21 h_v23 dropping h_v24 h_v25 hinv15 s15 v24 v25
  store_step with Store.apply_mk_rep s16 v23 v26 _ _ hinv16 h64 h_v23 h_v26 as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_v19 h_v21 dropping h_v23 h_v26 hinv16 s16 v23 v26
  store_step with Store.apply_mk_rep s17 v21 v27 _ _ hinv17 h64 h_v21 h_v27 as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_v19 dropping h_v21 h_v27 hinv17 s17 v21 v27
  store_step with Store.apply_mk_rep s18 v19 v28 _ _ hinv18 h64 h_v19 h_v28 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying dropping h_v19 h_v28 hinv18 s18 v19 v28
  case_done hinv19 hG with h_v29 in EoCases.__eo_prog_str_replace_empty.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_str_replace_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dempty.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_replace_empty x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_empty.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_empty
  unfold EoCases.__eo_prog_str_replace_empty.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dempty s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_empty x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dempty.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dempty_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_replace_empty.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dempty.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dempty s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_empty x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dempty_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_find_base.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_find_base.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v20 as ⟨v23, v24, x_v23, x_v24, h_v23, h_v24, hn_v23, hn_v24⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s2 e_v25 (by rw [he_v25]; exact empty_args) hinv2 h64 as ⟨v25, s3, hinv3, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v18 h_v21 h_v23 h_v24 dropping h_v13 h_v14 h_v15 h_v17 h_v20 he_v25 hinv2 e_v25 s2 v13 v14 v15 v17 v20
  pat_same v23 v25 with h_v23 h_v25 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v24 a0 with h_v24 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v21 a1 with h_v21 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v26, s4, hinv4, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v18 dropping h_v21 h_v23 h_v24 h_v25 hinv3 s3 v21 v23 v24 v25
  pat_same v18 v26 with h_v18 h_v26 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v27, s5, hinv5, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 dropping h_v18 h_v26 hinv4 s4 v18 v26
  pat_same v11 v27 with h_v11 h_v27 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v28, s6, hinv6, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v27 hinv5 s5 v11 v27
  pat_same v4 v28 with h_v4 h_v28 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v30, x_v30, h_v30⟩ else hinv6 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v30 as ⟨v32, v33, x_v32, x_v33, h_v32, h_v33, hn_v32, hn_v33⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v33 h_v35 h_v36 dropping h_a6 h_v28 h_v30 h_v32 h_v4 he_v37 hinv6 e_v37 s6 v28 v30 v32 v4
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v36 a3 with h_v36 h_a3 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v33 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v42 as ⟨v45, v46, x_v45, x_v46, h_v45, h_v46, hn_v45, hn_v46⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s7 e_v47 (by rw [he_v47]; exact empty_args) hinv7 h64 as ⟨v47, s8, hinv8, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v40 h_v43 h_v45 h_v46 dropping h_v33 h_v35 h_v36 h_v37 h_v39 h_v42 he_v47 hinv7 e_v47 s7 v33 v35 v36 v37 v39 v42
  pat_same v45 v47 with h_v45 h_v47 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v46 a0 with h_v46 h_a0 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v48, s9, hinv9, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v40 h_v43 dropping h_v45 h_v46 h_v47 hinv8 s8 v45 v46 v47
  pat_same v43 v48 with h_v43 h_v48 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v40 as ⟨v50, v51, x_v50, x_v51, h_v50, h_v51, hn_v50, hn_v51⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s9 e_v58 (by rw [he_v58]; exact empty_args) hinv9 h64 as ⟨v58, s10, hinv10, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v51 h_v54 h_v56 h_v57 dropping h_v40 h_v43 h_v48 h_v50 h_v53 he_v58 hinv9 e_v58 s9 v40 v43 v48 v50 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v57 a0 with h_v57 h_a0 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v54 a1 with h_v54 h_a1 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s10 0#u32 (0) (by scalar_tac) hinv10 h64 as ⟨v59, s11, hinv11, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v51 dropping h_v54 h_v56 h_v57 h_v58 hinv10 s10 v54 v56 v57 v58
  pat_same v51 v59 with h_v51 h_v59 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v61, x_v61, h_v61⟩ else hinv11 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v61 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v63 as ⟨v66, v67, x_v66, x_v67, h_v66, h_v67, hn_v66, hn_v67⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v68 (by rw [he_v68]; exact empty_args) hinv11 h64 as ⟨v68, s12, hinv12, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v64 h_v66 h_v67 dropping h_a7 h_v51 h_v59 h_v61 h_v63 he_v68 hinv11 e_v68 s11 v51 v59 v61 v63
  pat_same v66 v68 with h_v66 h_v68 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v67 a4 with h_v67 h_a4 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v64 as ⟨v70, v71, x_v70, x_v71, h_v70, h_v71, hn_v70, hn_v71⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v70 as ⟨v73, v74, x_v73, x_v74, h_v73, h_v74, hn_v73, hn_v74⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v73 as ⟨v76, v77, x_v76, x_v77, h_v76, h_v77, hn_v76, hn_v77⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s12 e_v78 (by rw [he_v78]; exact empty_args) hinv12 h64 as ⟨v78, s13, hinv13, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v74 h_v76 h_v77 dropping h_v64 h_v66 h_v67 h_v68 h_v70 h_v73 he_v78 hinv12 e_v78 s12 v64 v66 v67 v68 v70 v73
  pat_same v76 v78 with h_v76 h_v78 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v77 a0 with h_v77 h_a0 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v74 as ⟨v80, v81, x_v80, x_v81, h_v80, h_v81, hn_v80, hn_v81⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v80 as ⟨v83, v84, x_v83, x_v84, h_v83, h_v84, hn_v83, hn_v84⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v85, he_v85⟩
  store_step with CtorSpec.eo__2b.construct s13 e_v85 (by rw [he_v85]; exact empty_args) hinv13 h64 as ⟨v85, s14, hinv14, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v81 h_v83 h_v84 dropping h_v74 h_v76 h_v77 h_v78 h_v80 he_v85 hinv13 e_v85 s13 v74 v76 v77 v78 v80
  pat_same v83 v85 with h_v83 h_v85 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v84 as ⟨v87, v88, x_v87, x_v88, h_v87, h_v88, hn_v87, hn_v88⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v87 as ⟨v90, v91, x_v90, x_v91, h_v90, h_v91, hn_v90, hn_v91⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v90 as ⟨v93, v94, x_v93, x_v94, h_v93, h_v94, hn_v93, hn_v94⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v95, he_v95⟩
  store_step with CtorSpec.eo_str_2eindexof.construct s14 e_v95 (by rw [he_v95]; exact empty_args) hinv14 h64 as ⟨v95, s15, hinv15, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v81 h_v88 h_v91 h_v93 h_v94 dropping h_v83 h_v84 h_v85 h_v87 h_v90 he_v95 hinv14 e_v95 s14 v83 v84 v85 v87 v90
  pat_same v93 v95 with h_v93 h_v95 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v94 a0 with h_v94 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v91 a1 with h_v91 h_a1 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 0#u32 (0) (by scalar_tac) hinv15 h64 as ⟨v96, s16, hinv16, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v81 h_v88 dropping h_v91 h_v93 h_v94 h_v95 hinv15 s15 v91 v93 v94 v95
  pat_same v88 v96 with h_v88 h_v96 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v81 as ⟨v98, v99, x_v98, x_v99, h_v98, h_v99, hn_v98, hn_v99⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v98 as ⟨v101, v102, x_v101, x_v102, h_v101, h_v102, hn_v101, hn_v102⟩ using hinv16 else hinv16 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v103, he_v103⟩
  store_step with CtorSpec.eo__2b.construct s16 e_v103 (by rw [he_v103]; exact empty_args) hinv16 h64 as ⟨v103, s17, hinv17, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v99 h_v101 h_v102 dropping h_v81 h_v88 h_v96 h_v98 he_v103 hinv16 e_v103 s16 v81 v88 v96 v98
  pat_same v101 v103 with h_v101 h_v103 using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v102 as ⟨v105, v106, x_v105, x_v106, h_v105, h_v106, hn_v105, hn_v106⟩ using hinv17 else hinv17 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v107, he_v107⟩
  store_step with CtorSpec.eo_str_2elen.construct s17 e_v107 (by rw [he_v107]; exact empty_args) hinv17 h64 as ⟨v107, s18, hinv18, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v99 h_v105 h_v106 dropping h_v101 h_v102 h_v103 he_v107 hinv17 e_v107 s17 v101 v102 v103
  pat_same v105 v107 with h_v105 h_v107 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v106 a1 with h_v106 h_a1 using hinv18 else hinv18 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 0#u32 (0) (by scalar_tac) hinv18 h64 as ⟨v108, s19, hinv19, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v71 h_v99 dropping h_v105 h_v106 h_v107 hinv18 s18 v105 v106 v107
  pat_same v99 v108 with h_v99 h_v108 using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_unapply h_v71 as ⟨v110, v111, x_v110, x_v111, h_v110, h_v111, hn_v110, hn_v111⟩ using hinv19 else hinv19 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v112, he_v112⟩
  store_step with CtorSpec.eo_str_2elen.construct s19 e_v112 (by rw [he_v112]; exact empty_args) hinv19 h64 as ⟨v112, s20, hinv20, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v110 h_v111 dropping h_v108 h_v71 h_v99 he_v112 hinv19 e_v112 s19 v108 v71 v99
  pat_same v110 v112 with h_v110 h_v112 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  pat_same v111 a0 with h_v111 h_a0 using hinv20 else hinv20 hG in EoCases.__eo_prog_str_replace_find_base.case_0
  step as ⟨e_v113, he_v113⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v113 (by rw [he_v113]; exact empty_args) hinv20 h64 as ⟨v113, s21, hinv21, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v110 h_v111 h_v112 he_v113 hinv20 e_v113 s20 v110 v111 v112
  step as ⟨e_v114, he_v114⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s21 e_v114 (by rw [he_v114]; exact empty_args) hinv21 h64 as ⟨v114, s22, hinv22, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v113 dropping he_v114 hinv21 e_v114 s21
  store_step with Store.apply_rep s22 v114 a0 _ _ hinv22 h64 h_v114 h_a0 (by ns_tac) (by ns_tac) as ⟨v115, s23, hinv23, h_v115⟩ growing hG carrying h_a1 h_a2 h_a3 h_a4 h_v113 dropping h_a0 h_v114 hinv22 s22 v114
  store_step with Store.apply_rep s23 v115 a1 _ _ hinv23 h64 h_v115 h_a1 (by ns_tac) (by ns_tac) as ⟨v116, s24, hinv24, h_v116⟩ growing hG carrying h_a2 h_a3 h_a4 h_v113 dropping h_a1 h_v115 hinv23 s23 v115
  store_step with Store.apply_rep s24 v116 a2 _ _ hinv24 h64 h_v116 h_a2 (by ns_tac) (by ns_tac) as ⟨v117, s25, hinv25, h_v117⟩ growing hG carrying h_a2 h_a3 h_a4 h_v113 dropping h_v116 hinv24 s24 v116
  store_step with Store.apply_rep s25 v113 v117 _ _ hinv25 h64 h_v113 h_v117 (by ns_tac) (by ns_tac) as ⟨v118, s26, hinv26, h_v118⟩ growing hG carrying h_a2 h_a3 h_a4 dropping h_v113 h_v117 hinv25 s25 v113 v117
  step as ⟨e_v119, he_v119⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s26 e_v119 (by rw [he_v119]; exact empty_args) hinv26 h64 as ⟨v119, s27, hinv27, h_v119⟩ growing hG carrying h_a2 h_a3 h_a4 h_v118 dropping he_v119 hinv26 e_v119 s26
  store_step with Store.apply_rep s27 v119 a3 _ _ hinv27 h64 h_v119 h_a3 (by ns_tac) (by ns_tac) as ⟨v120, s28, hinv28, h_v120⟩ growing hG carrying h_a2 h_a3 h_a4 h_v118 dropping h_v119 hinv27 s27 v119
  step as ⟨e_v121, he_v121⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s28 e_v121 (by rw [he_v121]; exact empty_args) hinv28 h64 as ⟨v121, s29, hinv29, h_v121⟩ growing hG carrying h_a2 h_a3 h_a4 h_v118 h_v120 dropping he_v121 hinv28 e_v121 s28
  store_step with Store.apply_rep s29 v121 a2 _ _ hinv29 h64 h_v121 h_a2 (by ns_tac) (by ns_tac) as ⟨v122, s30, hinv30, h_v122⟩ growing hG carrying h_a3 h_a4 h_v118 h_v120 dropping h_a2 h_v121 hinv29 s29 v121
  step as ⟨e_v123, he_v123⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s30 e_v123 (by rw [he_v123]; exact empty_args) hinv30 h64 as ⟨v123, s31, hinv31, h_v123⟩ growing hG carrying h_a3 h_a4 h_v118 h_v120 h_v122 dropping he_v123 hinv30 e_v123 s30
  store_step with Store.apply_rep s31 v123 a4 _ _ hinv31 h64 h_v123 h_a4 (by ns_tac) (by ns_tac) as ⟨v124, s32, hinv32, h_v124⟩ growing hG carrying h_a3 h_v118 h_v120 h_v122 dropping h_a4 h_v123 hinv31 s31 v123
  step as ⟨e_v125, he_v125⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s32 e_v125 (by rw [he_v125]; exact empty_args) hinv32 h64 as ⟨v125, s33, hinv33, h_v125⟩ growing hG carrying h_a3 h_v118 h_v120 h_v122 h_v124 dropping he_v125 hinv32 e_v125 s32
  store_step with ih.eo__24eo_5ftypeof s33 a3 _ hinv33 h64 (hG.rem hrem) h_a3 as ⟨v126, s34, hinv34, h_v126⟩ growing hG carrying h_v118 h_v120 h_v122 h_v124 h_v125 dropping h_a3 hinv33 s33
  store_step with ih.eo__24eo_5fnil s34 v125 v126 _ _ hinv34 h64 (hG.rem hrem) h_v125 h_v126 as ⟨v127, s35, hinv35, h_v127⟩ growing hG carrying h_v118 h_v120 h_v122 h_v124 dropping h_v125 h_v126 hinv34 s34 v125 v126
  store_step with Store.apply_mk_rep s35 v124 v127 _ _ hinv35 h64 h_v124 h_v127 as ⟨v128, s36, hinv36, h_v128⟩ growing hG carrying h_v118 h_v120 h_v122 dropping h_v124 h_v127 hinv35 s35 v124 v127
  store_step with Store.apply_mk_rep s36 v122 v128 _ _ hinv36 h64 h_v122 h_v128 as ⟨v129, s37, hinv37, h_v129⟩ growing hG carrying h_v118 h_v120 dropping h_v122 h_v128 hinv36 s36 v122 v128
  store_step with Store.apply_mk_rep s37 v120 v129 _ _ hinv37 h64 h_v120 h_v129 as ⟨v130, s38, hinv38, h_v130⟩ growing hG carrying h_v118 dropping h_v120 h_v129 hinv37 s37 v120 v129
  store_step with Store.apply_mk_rep s38 v118 v130 _ _ hinv38 h64 h_v118 h_v130 as ⟨v131, s39, hinv39, h_v131⟩ growing hG carrying dropping h_v118 h_v130 hinv38 s38 v118 v130
  case_done hinv39 hG with h_v131 in EoCases.__eo_prog_str_replace_find_base.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v20 hn_v21 hn_v23 hn_v24 hn_v32 hn_v33 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v45 hn_v46 hn_v50 hn_v51 hn_v53 hn_v54 hn_v56 hn_v57 hn_v63 hn_v64 hn_v66 hn_v67 hn_v70 hn_v71 hn_v73 hn_v74 hn_v76 hn_v77 hn_v80 hn_v81 hn_v83 hn_v84 hn_v87 hn_v88 hn_v90 hn_v91 hn_v93 hn_v94 hn_v98 hn_v99 hn_v101 hn_v102 hn_v105 hn_v106 hn_v110 hn_v111

/-- logos's `__eo_prog_str_replace_find_base` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_str_replace_find_base x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_find_base.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_find_base
  unfold EoCases.__eo_prog_str_replace_find_base.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_find_base x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_replace_find_base.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_find_base x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dfind_2dbase_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2did_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2did s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_id.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_id.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2did
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 dropping h_a1 h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.apply_rep s6 v5 a0 _ _ hinv6 h64 h_v5 h_a0 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_a0 h_v5 hinv6 s6 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_str_replace_id.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_replace_id` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2did.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_replace_id x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_id.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_id
  unfold EoCases.__eo_prog_str_replace_id.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2did_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2did s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_id x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2did.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2did
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2did_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_id.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2did_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2did.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dreplace_2did
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2did s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_id x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2did_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_no_contains.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_no_contains.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v13 h_v14 h_v15 hinv2 s2 v11 v13 v14 v15
  pat_same v4 v16 with h_v4 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_replace_no_contains.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v16 h_v4 he_v17 hinv3 e_v17 s3 v16 v4
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping he_v18 hinv4 e_v18 s4
  store_step with Store.apply_rep s5 v18 a0 _ _ hinv5 h64 h_v18 h_a0 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v17 dropping h_v18 hinv5 s5 v18
  store_step with Store.apply_rep s6 v19 a1 _ _ hinv6 h64 h_v19 h_a1 (by ns_tac) (by ns_tac) as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a2 h_v17 dropping h_a1 h_v19 hinv6 s6 v19
  store_step with Store.apply_rep s7 v20 a2 _ _ hinv7 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_v17 dropping h_a2 h_v20 hinv7 s7 v20
  store_step with Store.apply_rep s8 v17 v21 _ _ hinv8 h64 h_v17 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 dropping h_v17 h_v21 hinv8 s8 v17 v21
  store_step with Store.apply_rep s9 v22 a0 _ _ hinv9 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying dropping h_a0 h_v22 hinv9 s9 v22
  case_done hinv10 hG with h_v23 in EoCases.__eo_prog_str_replace_no_contains.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_str_replace_no_contains` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_replace_no_contains x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_no_contains.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_no_contains
  unfold EoCases.__eo_prog_str_replace_no_contains.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_no_contains x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_replace_no_contains.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_no_contains x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dno_2dcontains_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dprefix s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_prefix.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_prefix.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dprefix
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v2 hinv3 s3 v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 dropping he_v4 hinv4 e_v4 s4
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v3 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v3 h_v6 hinv7 s7 v3 v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 h_v7 hinv8 s8 v1 v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a1 h_a2 h_a3 h_v0 dropping h_a0 h_v8 hinv9 s9 v8
  store_step with Store.apply_rep s10 v9 a3 _ _ hinv10 h64 h_v9 h_a3 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_a2 h_a3 h_v0 dropping h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v0 v10 _ _ hinv11 h64 h_v0 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a1 h_a2 h_a3 dropping h_v0 h_v10 hinv11 s11 v0 v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s12 e_v12 (by rw [he_v12]; exact empty_args) hinv12 h64 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a1 h_a2 h_a3 h_v11 dropping he_v12 hinv12 e_v12 s12
  store_step with Store.apply_rep s13 v12 a3 _ _ hinv13 h64 h_v12 h_a3 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a1 h_a2 h_v11 dropping h_a3 h_v12 hinv13 s13 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a1 h_a2 h_v11 h_v13 dropping he_v14 hinv14 e_v14 s14
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a2 h_v11 h_v13 dropping h_a1 h_v14 hinv15 s15 v14
  store_step with Store.apply_rep s16 v15 a2 _ _ hinv16 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_v11 h_v13 dropping h_a2 h_v15 hinv16 s16 v15
  store_step with Store.apply_rep s17 v13 v16 _ _ hinv17 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_v11 dropping h_v13 h_v16 hinv17 s17 v13 v16
  store_step with Store.apply_rep s18 v11 v17 _ _ hinv18 h64 h_v11 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying dropping h_v11 h_v17 hinv18 s18 v11 v17
  case_done hinv19 hG with h_v18 in EoCases.__eo_prog_str_replace_prefix.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

/-- logos's `__eo_prog_str_replace_prefix` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dprefix.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_replace_prefix x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_prefix.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_prefix
  unfold EoCases.__eo_prog_str_replace_prefix.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dprefix s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_prefix x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dprefix.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dprefix
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dprefix_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_replace_prefix.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dprefix_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dprefix.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dprefix
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dprefix s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_prefix x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dprefix_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_re_all_none.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_re_all_none.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre_5fall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2enone.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 dropping h_a1 h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 dropping h_v0 h_v5 hinv6 s6 v0 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_a0 h_v6 hinv7 s7 v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_str_replace_re_all_none.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_replace_re_all_none` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_replace_re_all_none x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_re_all_none.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_re_all_none
  unfold EoCases.__eo_prog_str_replace_re_all_none.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_re_all_none x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_re_all_none.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_re_all_none x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2dnone_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_re_none.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_re_none.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace_5fre.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_re_2enone.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v2 v3 _ _ hinv4 h64 h_v2 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v3 hinv4 s4 v2 v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 dropping h_a1 h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v0 v5 _ _ hinv6 h64 h_v0 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 dropping h_v0 h_v5 hinv6 s6 v0 v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying dropping h_a0 h_v6 hinv7 s7 v6
  case_done hinv8 hG with h_v7 in EoCases.__eo_prog_str_replace_re_none.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_replace_re_none` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_replace_re_none x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_re_none.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_re_none
  unfold EoCases.__eo_prog_str_replace_re_none.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_re_none x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_re_none.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_re_none x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dnone_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_self.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_self.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a1 h_v0 dropping h_a0 h_v2 hinv3 s3 v2
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a1 h_v0 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a1 dropping h_v0 h_v4 hinv5 s5 v0 v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying dropping h_a1 h_v5 hinv6 s6 v5
  case_done hinv7 hG with h_v6 in EoCases.__eo_prog_str_replace_self.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_replace_self` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dself.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_replace_self x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_self.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_self
  unfold EoCases.__eo_prog_str_replace_self.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dself_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dself s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_self x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dself.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dself
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_self.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dself_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dself.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dself
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dself s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_self x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dself_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_replace_self_ctn_simp.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_replace_self_ctn_simp.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2econtains.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0 dropping he_v1 hinv1 e_v1 s1
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v1 hinv2 s2 v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2ereplace.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v4 a0 _ _ hinv5 h64 h_v4 h_a0 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v4 hinv5 s5 v4
  store_step with Store.apply_rep s6 v5 a1 _ _ hinv6 h64 h_v5 h_a1 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 dropping h_v5 hinv6 s6 v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 dropping h_v2 h_v6 hinv7 s7 v2 v6
  store_step with Store.apply_rep s8 v0 v7 _ _ hinv8 h64 h_v0 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 dropping h_v0 h_v7 hinv8 s8 v0 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_str_2econtains.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v8 dropping he_v9 hinv9 e_v9 s9
  store_step with Store.apply_rep s10 v9 a0 _ _ hinv10 h64 h_v9 h_a0 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a1 h_v8 dropping h_a0 h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v10 a1 _ _ hinv11 h64 h_v10 h_a1 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_v8 dropping h_a1 h_v10 hinv11 s11 v10
  store_step with Store.apply_rep s12 v8 v11 _ _ hinv12 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying dropping h_v11 h_v8 hinv12 s12 v11 v8
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_str_replace_self_ctn_simp.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_str_replace_self_ctn_simp` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_str_replace_self_ctn_simp x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_replace_self_ctn_simp.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_replace_self_ctn_simp
  unfold EoCases.__eo_prog_str_replace_self_ctn_simp.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_replace_self_ctn_simp x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_str_replace_self_ctn_simp.case_0

theorem eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_str_replace_self_ctn_simp x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dreplace_2dself_2dctn_2dsimp_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_char_start_eq_len.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_char_start_eq_len.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a3 h_v1 h_v2 dropping h_a2 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v5, x_v5, h_v5⟩ else hinv1 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_unapply h_v5 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 h_v10 h_v11 dropping h_a3 h_v1 h_v3 h_v5 h_v7 he_v12 hinv1 e_v12 s1 v1 v3 v5 v7
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__3e_3d.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 h_v15 h_v17 h_v18 dropping h_v10 h_v11 h_v12 h_v14 he_v19 hinv2 e_v19 s2 v10 v11 v12 v14
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 h_v15 h_v18 dropping h_v17 h_v19 hinv3 s3 v17 v19
  pat_same v18 v20 with h_v18 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_unapply h_v15 as ⟨v22, v23, x_v22, x_v23, h_v22, h_v23, hn_v22, hn_v23⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v24 (by rw [he_v24]; exact empty_args) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 h_v22 h_v23 dropping h_v15 h_v18 h_v20 he_v24 hinv4 e_v24 s4 v15 v18 v20
  pat_same v22 v24 with h_v22 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  pat_same v23 a0 with h_v23 h_a0 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 h_v2 h_v8 dropping h_v22 h_v23 h_v24 hinv5 s5 v22 v23 v24
  pat_same v8 v25 with h_v8 h_v25 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_v2 dropping h_v25 h_v8 he_v26 hinv6 e_v26 s6 v25 v8
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s7 e_v27 (by rw [he_v27]; exact empty_args) hinv7 h64 as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_v2 h_v26 dropping he_v27 hinv7 e_v27 s7
  store_step with Store.apply_rep s8 v27 a0 _ _ hinv8 h64 h_v27 h_a0 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a1 h_v2 h_v26 dropping h_a0 h_v27 hinv8 s8 v27
  store_step with Store.apply_rep s9 v28 a1 _ _ hinv9 h64 h_v28 h_a1 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a1 h_v2 h_v26 dropping h_v28 hinv9 s9 v28
  store_step with Store.apply_rep s10 v29 a1 _ _ hinv10 h64 h_v29 h_a1 (by ns_tac) (by ns_tac) as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_v2 h_v26 dropping h_a1 h_v29 hinv10 s10 v29
  store_step with Store.apply_rep s11 v26 v30 _ _ hinv11 h64 h_v26 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_v2 dropping h_v26 h_v30 hinv11 s11 v26 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_Seq.construct s12 e_v32 (by rw [he_v32]; exact empty_args) hinv12 h64 as ⟨v32, s13, hinv13, h_v32⟩ growing hG carrying h_v2 h_v31 dropping he_v32 hinv12 e_v32 s12
  store_step with Store.apply_rep s13 v32 v2 _ _ hinv13 h64 h_v32 h_v2 (by ns_tac) (by ns_tac) as ⟨v33, s14, hinv14, h_v33⟩ growing hG carrying h_v31 dropping h_v2 h_v32 hinv13 s13 v2 v32
  store_step with ih.eo__24seq_5fempty s14 v33 _ hinv14 h64 (hG.rem hrem) h_v33 as ⟨v34, s15, hinv15, h_v34⟩ growing hG carrying h_v31 dropping h_v33 hinv14 s14 v33
  store_step with Store.apply_mk_rep s15 v31 v34 _ _ hinv15 h64 h_v31 h_v34 as ⟨v35, s16, hinv16, h_v35⟩ growing hG carrying dropping h_v31 h_v34 hinv15 s15 v31 v34
  case_done hinv16 hG with h_v35 in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v7 hn_v8 hn_v10 hn_v11 hn_v14 hn_v15 hn_v17 hn_v18 hn_v22 hn_v23

/-- logos's `__eo_prog_str_substr_char_start_eq_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_substr_char_start_eq_len x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_char_start_eq_len.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_char_start_eq_len
  unfold EoCases.__eo_prog_str_substr_char_start_eq_len.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_char_start_eq_len x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_substr_char_start_eq_len.case_0

theorem eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_substr_char_start_eq_len x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dsubstr_2dchar_2dstart_2deq_2dlen_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_combine1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_combine1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v24 h_v25 dropping h_a6 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 h_v31 h_v32 dropping h_v24 h_v25 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v24 v25 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_same v32 a3 with h_v32 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 dropping h_v31 h_v32 h_v33 hinv6 s6 v31 v32 v33
  pat_same v29 v34 with h_v29 h_v34 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 dropping h_v29 h_v34 hinv7 s7 v29 v34
  pat_same v22 v35 with h_v22 h_v35 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v37, x_v37, h_v37⟩ else hinv8 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v37 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v42 h_v43 dropping h_a7 h_v22 h_v35 h_v37 h_v39 he_v44 hinv8 e_v44 s8 v22 v35 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3e_3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v49 h_v50 dropping h_v42 h_v43 h_v44 h_v46 he_v51 hinv9 e_v51 s9 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v54 h_v56 h_v57 dropping h_v49 h_v50 h_v51 h_v53 he_v58 hinv10 e_v58 s10 v49 v50 v51 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_same v57 a4 with h_v57 h_a4 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v54 as ⟨v60, v61, x_v60, x_v61, h_v60, h_v61, hn_v60, hn_v61⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_unapply h_v60 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__2d.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v61 h_v63 h_v64 dropping h_v54 h_v56 h_v57 h_v58 h_v60 he_v65 hinv11 e_v65 s11 v54 v56 v57 v58 v60
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_same v64 a2 with h_v64 h_a2 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  pat_same v61 a3 with h_v61 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 dropping h_v61 h_v63 h_v64 h_v65 hinv12 s12 v61 v63 v64 v65
  pat_same v47 v66 with h_v47 h_v66 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  store_step with Store.literal_boolean_spec s13 true hinv13 h64 as ⟨v67, s14, hinv14, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 dropping h_v47 h_v66 hinv13 s13 v47 v66
  pat_same v40 v67 with h_v40 h_v67 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine1.case_0
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s14 e_v68 (by rw [he_v68]; exact empty_args) hinv14 h64 as ⟨v68, s15, hinv15, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v40 h_v67 he_v68 hinv14 e_v68 s14 v40 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s15 e_v69 (by rw [he_v69]; exact empty_args) hinv15 h64 as ⟨v69, s16, hinv16, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 dropping he_v69 hinv15 e_v69 s15
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s16 e_v70 (by rw [he_v70]; exact empty_args) hinv16 h64 as ⟨v70, s17, hinv17, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping he_v70 hinv16 e_v70 s16
  store_step with Store.apply_rep s17 v70 a0 _ _ hinv17 h64 h_v70 h_a0 (by ns_tac) (by ns_tac) as ⟨v71, s18, hinv18, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping h_v70 hinv17 s17 v70
  store_step with Store.apply_rep s18 v71 a1 _ _ hinv18 h64 h_v71 h_a1 (by ns_tac) (by ns_tac) as ⟨v72, s19, hinv19, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping h_v71 hinv18 s18 v71
  store_step with Store.apply_rep s19 v72 a2 _ _ hinv19 h64 h_v72 h_a2 (by ns_tac) (by ns_tac) as ⟨v73, s20, hinv20, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping h_v72 hinv19 s19 v72
  store_step with Store.apply_rep s20 v69 v73 _ _ hinv20 h64 h_v69 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s21, hinv21, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 dropping h_v69 h_v73 hinv20 s20 v69 v73
  store_step with Store.apply_rep s21 v74 a3 _ _ hinv21 h64 h_v74 h_a3 (by ns_tac) (by ns_tac) as ⟨v75, s22, hinv22, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 dropping h_v74 hinv21 s21 v74
  store_step with Store.apply_rep s22 v75 a4 _ _ hinv22 h64 h_v75 h_a4 (by ns_tac) (by ns_tac) as ⟨v76, s23, hinv23, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v68 dropping h_a4 h_v75 hinv22 s22 v75
  store_step with Store.apply_rep s23 v68 v76 _ _ hinv23 h64 h_v68 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s24, hinv24, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v68 h_v76 hinv23 s23 v68 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s24 e_v78 (by rw [he_v78]; exact empty_args) hinv24 h64 as ⟨v78, s25, hinv25, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v77 dropping he_v78 hinv24 e_v78 s24
  store_step with Store.apply_rep s25 v78 a0 _ _ hinv25 h64 h_v78 h_a0 (by ns_tac) (by ns_tac) as ⟨v79, s26, hinv26, h_v79⟩ growing hG carrying h_a1 h_a2 h_a3 h_v77 dropping h_a0 h_v78 hinv25 s25 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo__2b.construct s26 e_v80 (by rw [he_v80]; exact empty_args) hinv26 h64 as ⟨v80, s27, hinv27, h_v80⟩ growing hG carrying h_a1 h_a2 h_a3 h_v77 h_v79 dropping he_v80 hinv26 e_v80 s26
  store_step with Store.apply_rep s27 v80 a1 _ _ hinv27 h64 h_v80 h_a1 (by ns_tac) (by ns_tac) as ⟨v81, s28, hinv28, h_v81⟩ growing hG carrying h_a2 h_a3 h_v77 h_v79 dropping h_a1 h_v80 hinv27 s27 v80
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__2b.construct s28 e_v82 (by rw [he_v82]; exact empty_args) hinv28 h64 as ⟨v82, s29, hinv29, h_v82⟩ growing hG carrying h_a2 h_a3 h_v77 h_v79 h_v81 dropping he_v82 hinv28 e_v82 s28
  store_step with Store.apply_rep s29 v82 a3 _ _ hinv29 h64 h_v82 h_a3 (by ns_tac) (by ns_tac) as ⟨v83, s30, hinv30, h_v83⟩ growing hG carrying h_a2 h_a3 h_v77 h_v79 h_v81 dropping h_v82 hinv29 s29 v82
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s30 0#u32 (0) (by scalar_tac) hinv30 h64 as ⟨v84, s31, hinv31, h_v84⟩ growing hG carrying h_a2 h_a3 h_v77 h_v79 h_v81 h_v83 dropping hinv30 s30
  store_step with Store.apply_rep s31 v83 v84 _ _ hinv31 h64 h_v83 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s32, hinv32, h_v85⟩ growing hG carrying h_a2 h_a3 h_v77 h_v79 h_v81 dropping h_v83 h_v84 hinv31 s31 v83 v84
  store_step with Store.apply_rep s32 v81 v85 _ _ hinv32 h64 h_v81 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s33, hinv33, h_v86⟩ growing hG carrying h_a2 h_a3 h_v77 h_v79 dropping h_v81 h_v85 hinv32 s32 v81 v85
  store_step with Store.apply_rep s33 v79 v86 _ _ hinv33 h64 h_v79 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s34, hinv34, h_v87⟩ growing hG carrying h_a2 h_a3 h_v77 dropping h_v79 h_v86 hinv33 s33 v79 v86
  step as ⟨e_v88, he_v88⟩
  store_step with CtorSpec.eo__2d.construct s34 e_v88 (by rw [he_v88]; exact empty_args) hinv34 h64 as ⟨v88, s35, hinv35, h_v88⟩ growing hG carrying h_a2 h_a3 h_v77 h_v87 dropping he_v88 hinv34 e_v88 s34
  store_step with Store.apply_rep s35 v88 a2 _ _ hinv35 h64 h_v88 h_a2 (by ns_tac) (by ns_tac) as ⟨v89, s36, hinv36, h_v89⟩ growing hG carrying h_a3 h_v77 h_v87 dropping h_a2 h_v88 hinv35 s35 v88
  store_step with Store.apply_rep s36 v89 a3 _ _ hinv36 h64 h_v89 h_a3 (by ns_tac) (by ns_tac) as ⟨v90, s37, hinv37, h_v90⟩ growing hG carrying h_v77 h_v87 dropping h_a3 h_v89 hinv36 s36 v89
  store_step with Store.apply_rep s37 v87 v90 _ _ hinv37 h64 h_v87 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s38, hinv38, h_v91⟩ growing hG carrying h_v77 dropping h_v87 h_v90 hinv37 s37 v87 v90
  store_step with Store.apply_rep s38 v77 v91 _ _ hinv38 h64 h_v77 h_v91 (by ns_tac) (by ns_tac) as ⟨v92, s39, hinv39, h_v92⟩ growing hG carrying dropping h_v77 h_v91 hinv38 s38 v77 v91
  case_done hinv39 hG with h_v92 in EoCases.__eo_prog_str_substr_combine1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57 hn_v60 hn_v61 hn_v63 hn_v64

/-- logos's `__eo_prog_str_substr_combine1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_str_substr_combine1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_combine1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_combine1
  unfold EoCases.__eo_prog_str_substr_combine1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_combine1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_substr_combine1.case_0

theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1 s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_str_substr_combine1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_combine2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_combine2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v24 h_v25 dropping h_a6 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 h_v31 h_v32 dropping h_v24 h_v25 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v24 v25 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_same v32 a3 with h_v32 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 dropping h_v31 h_v32 h_v33 hinv6 s6 v31 v32 v33
  pat_same v29 v34 with h_v29 h_v34 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 dropping h_v29 h_v34 hinv7 s7 v29 v34
  pat_same v22 v35 with h_v22 h_v35 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v37, x_v37, h_v37⟩ else hinv8 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v37 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v42 h_v43 dropping h_a7 h_v22 h_v35 h_v37 h_v39 he_v44 hinv8 e_v44 s8 v22 v35 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3e_3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v49 h_v50 dropping h_v42 h_v43 h_v44 h_v46 he_v51 hinv9 e_v51 s9 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__2d.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v54 h_v56 h_v57 dropping h_v49 h_v50 h_v51 h_v53 he_v58 hinv10 e_v58 s10 v49 v50 v51 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v57 as ⟨v60, v61, x_v60, x_v61, h_v60, h_v61, hn_v60, hn_v61⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_unapply h_v60 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__2d.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v54 h_v61 h_v63 h_v64 dropping h_v56 h_v57 h_v58 h_v60 he_v65 hinv11 e_v65 s11 v56 v57 v58 v60
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_same v64 a2 with h_v64 h_a2 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_same v61 a3 with h_v61 h_a3 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  pat_same v54 a4 with h_v54 h_a4 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 dropping h_v54 h_v61 h_v63 h_v64 h_v65 hinv12 s12 v54 v61 v63 v64 v65
  pat_same v47 v66 with h_v47 h_v66 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  store_step with Store.literal_boolean_spec s13 true hinv13 h64 as ⟨v67, s14, hinv14, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 dropping h_v47 h_v66 hinv13 s13 v47 v66
  pat_same v40 v67 with h_v40 h_v67 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine2.case_0
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__3d.construct s14 e_v68 (by rw [he_v68]; exact empty_args) hinv14 h64 as ⟨v68, s15, hinv15, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v40 h_v67 he_v68 hinv14 e_v68 s14 v40 v67
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s15 e_v69 (by rw [he_v69]; exact empty_args) hinv15 h64 as ⟨v69, s16, hinv16, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 dropping he_v69 hinv15 e_v69 s15
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s16 e_v70 (by rw [he_v70]; exact empty_args) hinv16 h64 as ⟨v70, s17, hinv17, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping he_v70 hinv16 e_v70 s16
  store_step with Store.apply_rep s17 v70 a0 _ _ hinv17 h64 h_v70 h_a0 (by ns_tac) (by ns_tac) as ⟨v71, s18, hinv18, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping h_v70 hinv17 s17 v70
  store_step with Store.apply_rep s18 v71 a1 _ _ hinv18 h64 h_v71 h_a1 (by ns_tac) (by ns_tac) as ⟨v72, s19, hinv19, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v68 h_v69 dropping h_v71 hinv18 s18 v71
  store_step with Store.apply_rep s19 v72 a2 _ _ hinv19 h64 h_v72 h_a2 (by ns_tac) (by ns_tac) as ⟨v73, s20, hinv20, h_v73⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v68 h_v69 dropping h_a2 h_v72 hinv19 s19 v72
  store_step with Store.apply_rep s20 v69 v73 _ _ hinv20 h64 h_v69 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s21, hinv21, h_v74⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v68 dropping h_v69 h_v73 hinv20 s20 v69 v73
  store_step with Store.apply_rep s21 v74 a3 _ _ hinv21 h64 h_v74 h_a3 (by ns_tac) (by ns_tac) as ⟨v75, s22, hinv22, h_v75⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v68 dropping h_v74 hinv21 s21 v74
  store_step with Store.apply_rep s22 v75 a4 _ _ hinv22 h64 h_v75 h_a4 (by ns_tac) (by ns_tac) as ⟨v76, s23, hinv23, h_v76⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v68 dropping h_v75 hinv22 s22 v75
  store_step with Store.apply_rep s23 v68 v76 _ _ hinv23 h64 h_v68 h_v76 (by ns_tac) (by ns_tac) as ⟨v77, s24, hinv24, h_v77⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 dropping h_v68 h_v76 hinv23 s23 v68 v76
  step as ⟨e_v78, he_v78⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s24 e_v78 (by rw [he_v78]; exact empty_args) hinv24 h64 as ⟨v78, s25, hinv25, h_v78⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v77 dropping he_v78 hinv24 e_v78 s24
  store_step with Store.apply_rep s25 v78 a0 _ _ hinv25 h64 h_v78 h_a0 (by ns_tac) (by ns_tac) as ⟨v79, s26, hinv26, h_v79⟩ growing hG carrying h_a1 h_a3 h_a4 h_v77 dropping h_a0 h_v78 hinv25 s25 v78
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo__2b.construct s26 e_v80 (by rw [he_v80]; exact empty_args) hinv26 h64 as ⟨v80, s27, hinv27, h_v80⟩ growing hG carrying h_a1 h_a3 h_a4 h_v77 h_v79 dropping he_v80 hinv26 e_v80 s26
  store_step with Store.apply_rep s27 v80 a1 _ _ hinv27 h64 h_v80 h_a1 (by ns_tac) (by ns_tac) as ⟨v81, s28, hinv28, h_v81⟩ growing hG carrying h_a3 h_a4 h_v77 h_v79 dropping h_a1 h_v80 hinv27 s27 v80
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__2b.construct s28 e_v82 (by rw [he_v82]; exact empty_args) hinv28 h64 as ⟨v82, s29, hinv29, h_v82⟩ growing hG carrying h_a3 h_a4 h_v77 h_v79 h_v81 dropping he_v82 hinv28 e_v82 s28
  store_step with Store.apply_rep s29 v82 a3 _ _ hinv29 h64 h_v82 h_a3 (by ns_tac) (by ns_tac) as ⟨v83, s30, hinv30, h_v83⟩ growing hG carrying h_a4 h_v77 h_v79 h_v81 dropping h_a3 h_v82 hinv29 s29 v82
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s30 0#u32 (0) (by scalar_tac) hinv30 h64 as ⟨v84, s31, hinv31, h_v84⟩ growing hG carrying h_a4 h_v77 h_v79 h_v81 h_v83 dropping hinv30 s30
  store_step with Store.apply_rep s31 v83 v84 _ _ hinv31 h64 h_v83 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s32, hinv32, h_v85⟩ growing hG carrying h_a4 h_v77 h_v79 h_v81 dropping h_v83 h_v84 hinv31 s31 v83 v84
  store_step with Store.apply_rep s32 v81 v85 _ _ hinv32 h64 h_v81 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s33, hinv33, h_v86⟩ growing hG carrying h_a4 h_v77 h_v79 dropping h_v81 h_v85 hinv32 s32 v81 v85
  store_step with Store.apply_rep s33 v79 v86 _ _ hinv33 h64 h_v79 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s34, hinv34, h_v87⟩ growing hG carrying h_a4 h_v77 dropping h_v79 h_v86 hinv33 s33 v79 v86
  store_step with Store.apply_rep s34 v87 a4 _ _ hinv34 h64 h_v87 h_a4 (by ns_tac) (by ns_tac) as ⟨v88, s35, hinv35, h_v88⟩ growing hG carrying h_v77 dropping h_a4 h_v87 hinv34 s34 v87
  store_step with Store.apply_rep s35 v77 v88 _ _ hinv35 h64 h_v77 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s36, hinv36, h_v89⟩ growing hG carrying dropping h_v77 h_v88 hinv35 s35 v77 v88
  case_done hinv36 hG with h_v89 in EoCases.__eo_prog_str_substr_combine2.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57 hn_v60 hn_v61 hn_v63 hn_v64

/-- logos's `__eo_prog_str_substr_combine2` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_str_substr_combine2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_combine2.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_combine2
  unfold EoCases.__eo_prog_str_substr_combine2.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_combine2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_substr_combine2.case_0

theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2 s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_str_substr_combine2 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine2_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_combine3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_combine3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v24 h_v25 dropping h_a6 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 h_v31 h_v32 dropping h_v24 h_v25 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v24 v25 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v32 a3 with h_v32 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 dropping h_v31 h_v32 h_v33 hinv6 s6 v31 v32 v33
  pat_same v29 v34 with h_v29 h_v34 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 dropping h_v29 h_v34 hinv7 s7 v29 v34
  pat_same v22 v35 with h_v22 h_v35 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v37, x_v37, h_v37⟩ else hinv8 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v37 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v42 h_v43 dropping h_a7 h_v22 h_v35 h_v37 h_v39 he_v44 hinv8 e_v44 s8 v22 v35 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3e_3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v49 h_v50 dropping h_v42 h_v43 h_v44 h_v46 he_v51 hinv9 e_v51 s9 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_str_2elen.construct s10 e_v55 (by rw [he_v55]; exact empty_args) hinv10 h64 as ⟨v55, s11, hinv11, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v53 h_v54 dropping h_v49 h_v50 h_v51 he_v55 hinv10 e_v55 s10 v49 v50 v51
  pat_same v53 v55 with h_v53 h_v55 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v54 as ⟨v57, v58, x_v57, x_v58, h_v57, h_v58, hn_v57, hn_v58⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v57 as ⟨v60, v61, x_v60, x_v61, h_v60, h_v61, hn_v60, hn_v61⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v60 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v58 h_v61 h_v63 h_v64 dropping h_v53 h_v54 h_v55 h_v57 h_v60 he_v65 hinv11 e_v65 s11 v53 v54 v55 v57 v60
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v64 a0 with h_v64 h_a0 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v61 a1 with h_v61 h_a1 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v58 a2 with h_v58 h_a2 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v47 as ⟨v67, v68, x_v67, x_v68, h_v67, h_v68, hn_v67, hn_v68⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v67 as ⟨v70, v71, x_v70, x_v71, h_v70, h_v71, hn_v70, hn_v71⟩ using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v72, he_v72⟩
  store_step with CtorSpec.eo__2b.construct s12 e_v72 (by rw [he_v72]; exact empty_args) hinv12 h64 as ⟨v72, s13, hinv13, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v68 h_v70 h_v71 dropping h_v47 h_v58 h_v61 h_v63 h_v64 h_v65 h_v67 he_v72 hinv12 e_v72 s12 v47 v58 v61 v63 v64 v65 v67
  pat_same v70 v72 with h_v70 h_v72 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v71 a3 with h_v71 h_a3 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v68 as ⟨v74, v75, x_v74, x_v75, h_v74, h_v75, hn_v74, hn_v75⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_unapply h_v74 as ⟨v77, v78, x_v77, x_v78, h_v77, h_v78, hn_v77, hn_v78⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v79, he_v79⟩
  store_step with CtorSpec.eo__2b.construct s13 e_v79 (by rw [he_v79]; exact empty_args) hinv13 h64 as ⟨v79, s14, hinv14, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v75 h_v77 h_v78 dropping h_v68 h_v70 h_v71 h_v72 h_v74 he_v79 hinv13 e_v79 s13 v68 v70 v71 v72 v74
  pat_same v77 v79 with h_v77 h_v79 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  pat_same v78 a4 with h_v78 h_a4 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 0#u32 (0) (by scalar_tac) hinv14 h64 as ⟨v80, s15, hinv15, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v75 dropping h_v77 h_v78 h_v79 hinv14 s14 v77 v78 v79
  pat_same v75 v80 with h_v75 h_v80 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v81, s16, hinv16, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 dropping h_v75 h_v80 hinv15 s15 v75 v80
  pat_same v40 v81 with h_v40 h_v81 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_substr_combine3.case_0
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v82 (by rw [he_v82]; exact empty_args) hinv16 h64 as ⟨v82, s17, hinv17, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v40 h_v81 he_v82 hinv16 e_v82 s16 v40 v81
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s17 e_v83 (by rw [he_v83]; exact empty_args) hinv17 h64 as ⟨v83, s18, hinv18, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 dropping he_v83 hinv17 e_v83 s17
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s18 e_v84 (by rw [he_v84]; exact empty_args) hinv18 h64 as ⟨v84, s19, hinv19, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping he_v84 hinv18 e_v84 s18
  store_step with Store.apply_rep s19 v84 a0 _ _ hinv19 h64 h_v84 h_a0 (by ns_tac) (by ns_tac) as ⟨v85, s20, hinv20, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping h_v84 hinv19 s19 v84
  store_step with Store.apply_rep s20 v85 a1 _ _ hinv20 h64 h_v85 h_a1 (by ns_tac) (by ns_tac) as ⟨v86, s21, hinv21, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping h_v85 hinv20 s20 v85
  store_step with Store.apply_rep s21 v86 a2 _ _ hinv21 h64 h_v86 h_a2 (by ns_tac) (by ns_tac) as ⟨v87, s22, hinv22, h_v87⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v82 h_v83 dropping h_a2 h_v86 hinv21 s21 v86
  store_step with Store.apply_rep s22 v83 v87 _ _ hinv22 h64 h_v83 h_v87 (by ns_tac) (by ns_tac) as ⟨v88, s23, hinv23, h_v88⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v82 dropping h_v83 h_v87 hinv22 s22 v83 v87
  store_step with Store.apply_rep s23 v88 a3 _ _ hinv23 h64 h_v88 h_a3 (by ns_tac) (by ns_tac) as ⟨v89, s24, hinv24, h_v89⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v82 dropping h_v88 hinv23 s23 v88
  store_step with Store.apply_rep s24 v89 a4 _ _ hinv24 h64 h_v89 h_a4 (by ns_tac) (by ns_tac) as ⟨v90, s25, hinv25, h_v90⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v82 dropping h_v89 hinv24 s24 v89
  store_step with Store.apply_rep s25 v82 v90 _ _ hinv25 h64 h_v82 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s26, hinv26, h_v91⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 dropping h_v82 h_v90 hinv25 s25 v82 v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s26 e_v92 (by rw [he_v92]; exact empty_args) hinv26 h64 as ⟨v92, s27, hinv27, h_v92⟩ growing hG carrying h_a0 h_a1 h_a3 h_a4 h_v91 dropping he_v92 hinv26 e_v92 s26
  store_step with Store.apply_rep s27 v92 a0 _ _ hinv27 h64 h_v92 h_a0 (by ns_tac) (by ns_tac) as ⟨v93, s28, hinv28, h_v93⟩ growing hG carrying h_a1 h_a3 h_a4 h_v91 dropping h_a0 h_v92 hinv27 s27 v92
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo__2b.construct s28 e_v94 (by rw [he_v94]; exact empty_args) hinv28 h64 as ⟨v94, s29, hinv29, h_v94⟩ growing hG carrying h_a1 h_a3 h_a4 h_v91 h_v93 dropping he_v94 hinv28 e_v94 s28
  store_step with Store.apply_rep s29 v94 a1 _ _ hinv29 h64 h_v94 h_a1 (by ns_tac) (by ns_tac) as ⟨v95, s30, hinv30, h_v95⟩ growing hG carrying h_a3 h_a4 h_v91 h_v93 dropping h_a1 h_v94 hinv29 s29 v94
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo__2b.construct s30 e_v96 (by rw [he_v96]; exact empty_args) hinv30 h64 as ⟨v96, s31, hinv31, h_v96⟩ growing hG carrying h_a3 h_a4 h_v91 h_v93 h_v95 dropping he_v96 hinv30 e_v96 s30
  store_step with Store.apply_rep s31 v96 a3 _ _ hinv31 h64 h_v96 h_a3 (by ns_tac) (by ns_tac) as ⟨v97, s32, hinv32, h_v97⟩ growing hG carrying h_a4 h_v91 h_v93 h_v95 dropping h_a3 h_v96 hinv31 s31 v96
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v98, s33, hinv33, h_v98⟩ growing hG carrying h_a4 h_v91 h_v93 h_v95 h_v97 dropping hinv32 s32
  store_step with Store.apply_rep s33 v97 v98 _ _ hinv33 h64 h_v97 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s34, hinv34, h_v99⟩ growing hG carrying h_a4 h_v91 h_v93 h_v95 dropping h_v97 h_v98 hinv33 s33 v97 v98
  store_step with Store.apply_rep s34 v95 v99 _ _ hinv34 h64 h_v95 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s35, hinv35, h_v100⟩ growing hG carrying h_a4 h_v91 h_v93 dropping h_v95 h_v99 hinv34 s34 v95 v99
  store_step with Store.apply_rep s35 v93 v100 _ _ hinv35 h64 h_v93 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s36, hinv36, h_v101⟩ growing hG carrying h_a4 h_v91 dropping h_v100 h_v93 hinv35 s35 v100 v93
  store_step with Store.apply_rep s36 v101 a4 _ _ hinv36 h64 h_v101 h_a4 (by ns_tac) (by ns_tac) as ⟨v102, s37, hinv37, h_v102⟩ growing hG carrying h_v91 dropping h_a4 h_v101 hinv36 s36 v101
  store_step with Store.apply_rep s37 v91 v102 _ _ hinv37 h64 h_v91 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s38, hinv38, h_v103⟩ growing hG carrying dropping h_v102 h_v91 hinv37 s37 v102 v91
  case_done hinv38 hG with h_v103 in EoCases.__eo_prog_str_substr_combine3.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v57 hn_v58 hn_v60 hn_v61 hn_v63 hn_v64 hn_v67 hn_v68 hn_v70 hn_v71 hn_v74 hn_v75 hn_v77 hn_v78

/-- logos's `__eo_prog_str_substr_combine3` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_str_substr_combine3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_combine3.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_combine3
  unfold EoCases.__eo_prog_str_substr_combine3.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) :
    body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_combine3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5) (by valid_tac hinv h_a6) (by valid_tac hinv h_a7)]
  unfold body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  stuck_check h_a4 : x_a4 as hn_a4 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3_spec n ih s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hc0 in EoCases.__eo_prog_str_substr_combine3.case_0

theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
  unfold eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3 s1 a0 a1 a2 a3 a4 a5 a6 a7) (fun s' t => Represents.rep s' t (__eo_prog_str_substr_combine3 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine3_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 a6 a7 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn) (by congr_one h_a6 hn) (by congr_one h_a7 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 a6 a7 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (h_a6 : Represents.rep s a6 x_a6) (h_a7 : Represents.rep s a7 x_a7) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) (hn_a4 : x_a4 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4 s a0 a1 a2 a3 a4 a5 a6 a7 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_combine4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_combine4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v6 h_v7 dropping h_a5 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v14 a1 with h_v14 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a6 h_a7 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a6 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v24 h_v25 dropping h_a6 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 h_v31 h_v32 dropping h_v24 h_v25 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v24 v25 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v32 a3 with h_v32 h_a3 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v34, s7, hinv7, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 h_v29 dropping h_v31 h_v32 h_v33 hinv6 s6 v31 v32 v33
  pat_same v29 v34 with h_v29 h_v34 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  store_step with Store.literal_boolean_spec s7 true hinv7 h64 as ⟨v35, s8, hinv8, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a7 h_v22 dropping h_v29 h_v34 hinv7 s7 v29 v34
  pat_same v22 v35 with h_v22 h_v35 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a7 as ⟨v37, x_v37, h_v37⟩ else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v37 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__3d.construct s8 e_v44 (by rw [he_v44]; exact empty_args) hinv8 h64 as ⟨v44, s9, hinv9, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v42 h_v43 dropping h_a7 h_v22 h_v35 h_v37 h_v39 he_v44 hinv8 e_v44 s8 v22 v35 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v43 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__3e_3d.construct s9 e_v51 (by rw [he_v51]; exact empty_args) hinv9 h64 as ⟨v51, s10, hinv10, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v49 h_v50 dropping h_v42 h_v43 h_v44 h_v46 he_v51 hinv9 e_v51 s9 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v50 as ⟨v53, v54, x_v53, x_v54, h_v53, h_v54, hn_v53, hn_v54⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v53 as ⟨v56, v57, x_v56, x_v57, h_v56, h_v57, hn_v56, hn_v57⟩ using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo__2b.construct s10 e_v58 (by rw [he_v58]; exact empty_args) hinv10 h64 as ⟨v58, s11, hinv11, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v54 h_v56 h_v57 dropping h_v49 h_v50 h_v51 h_v53 he_v58 hinv10 e_v58 s10 v49 v50 v51 v53
  pat_same v56 v58 with h_v56 h_v58 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v57 a3 with h_v57 h_a3 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v54 as ⟨v60, v61, x_v60, x_v61, h_v60, h_v61, hn_v60, hn_v61⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v60 as ⟨v63, v64, x_v63, x_v64, h_v63, h_v64, hn_v63, hn_v64⟩ using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo__2b.construct s11 e_v65 (by rw [he_v65]; exact empty_args) hinv11 h64 as ⟨v65, s12, hinv12, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v61 h_v63 h_v64 dropping h_v54 h_v56 h_v57 h_v58 h_v60 he_v65 hinv11 e_v65 s11 v54 v56 v57 v58 v60
  pat_same v63 v65 with h_v63 h_v65 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v64 a4 with h_v64 h_a4 using hinv12 else hinv12 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v66, s13, hinv13, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v47 h_v61 dropping h_v63 h_v64 h_v65 hinv12 s12 v63 v64 v65
  pat_same v61 v66 with h_v61 h_v66 using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v47 as ⟨v68, v69, x_v68, x_v69, h_v68, h_v69, hn_v68, hn_v69⟩ using hinv13 else hinv13 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v70, he_v70⟩
  store_step with CtorSpec.eo_str_2elen.construct s13 e_v70 (by rw [he_v70]; exact empty_args) hinv13 h64 as ⟨v70, s14, hinv14, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v68 h_v69 dropping h_v47 h_v61 h_v66 he_v70 hinv13 e_v70 s13 v47 v61 v66
  pat_same v68 v70 with h_v68 h_v70 using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v69 as ⟨v72, v73, x_v72, x_v73, h_v72, h_v73, hn_v72, hn_v73⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v72 as ⟨v75, v76, x_v75, x_v76, h_v75, h_v76, hn_v75, hn_v76⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_unapply h_v75 as ⟨v78, v79, x_v78, x_v79, h_v78, h_v79, hn_v78, hn_v79⟩ using hinv14 else hinv14 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v80, he_v80⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s14 e_v80 (by rw [he_v80]; exact empty_args) hinv14 h64 as ⟨v80, s15, hinv15, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 h_v73 h_v76 h_v78 h_v79 dropping h_v68 h_v69 h_v70 h_v72 h_v75 he_v80 hinv14 e_v80 s14 v68 v69 v70 v72 v75
  pat_same v78 v80 with h_v78 h_v80 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v79 a0 with h_v79 h_a0 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v76 a1 with h_v76 h_a1 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  pat_same v73 a2 with h_v73 h_a2 using hinv15 else hinv15 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  store_step with Store.literal_boolean_spec s15 true hinv15 h64 as ⟨v81, s16, hinv16, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v40 dropping h_v73 h_v76 h_v78 h_v79 h_v80 hinv15 s15 v73 v76 v78 v79 v80
  pat_same v40 v81 with h_v40 h_v81 using hinv16 else hinv16 hG in EoCases.__eo_prog_str_substr_combine4.case_0
  step as ⟨e_v82, he_v82⟩
  store_step with CtorSpec.eo__3d.construct s16 e_v82 (by rw [he_v82]; exact empty_args) hinv16 h64 as ⟨v82, s17, hinv17, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 dropping h_v40 h_v81 he_v82 hinv16 e_v82 s16 v40 v81
  step as ⟨e_v83, he_v83⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s17 e_v83 (by rw [he_v83]; exact empty_args) hinv17 h64 as ⟨v83, s18, hinv18, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 dropping he_v83 hinv17 e_v83 s17
  step as ⟨e_v84, he_v84⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s18 e_v84 (by rw [he_v84]; exact empty_args) hinv18 h64 as ⟨v84, s19, hinv19, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping he_v84 hinv18 e_v84 s18
  store_step with Store.apply_rep s19 v84 a0 _ _ hinv19 h64 h_v84 h_a0 (by ns_tac) (by ns_tac) as ⟨v85, s20, hinv20, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping h_v84 hinv19 s19 v84
  store_step with Store.apply_rep s20 v85 a1 _ _ hinv20 h64 h_v85 h_a1 (by ns_tac) (by ns_tac) as ⟨v86, s21, hinv21, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping h_v85 hinv20 s20 v85
  store_step with Store.apply_rep s21 v86 a2 _ _ hinv21 h64 h_v86 h_a2 (by ns_tac) (by ns_tac) as ⟨v87, s22, hinv22, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 h_v83 dropping h_v86 hinv21 s21 v86
  store_step with Store.apply_rep s22 v83 v87 _ _ hinv22 h64 h_v83 h_v87 (by ns_tac) (by ns_tac) as ⟨v88, s23, hinv23, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 dropping h_v83 h_v87 hinv22 s22 v83 v87
  store_step with Store.apply_rep s23 v88 a3 _ _ hinv23 h64 h_v88 h_a3 (by ns_tac) (by ns_tac) as ⟨v89, s24, hinv24, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v82 dropping h_v88 hinv23 s23 v88
  store_step with Store.apply_rep s24 v89 a4 _ _ hinv24 h64 h_v89 h_a4 (by ns_tac) (by ns_tac) as ⟨v90, s25, hinv25, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v82 dropping h_a4 h_v89 hinv24 s24 v89
  store_step with Store.apply_rep s25 v82 v90 _ _ hinv25 h64 h_v82 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s26, hinv26, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v82 h_v90 hinv25 s25 v82 v90
  step as ⟨e_v92, he_v92⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s26 e_v92 (by rw [he_v92]; exact empty_args) hinv26 h64 as ⟨v92, s27, hinv27, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v91 dropping he_v92 hinv26 e_v92 s26
  store_step with Store.apply_rep s27 v92 a0 _ _ hinv27 h64 h_v92 h_a0 (by ns_tac) (by ns_tac) as ⟨v93, s28, hinv28, h_v93⟩ growing hG carrying h_a1 h_a2 h_a3 h_v91 dropping h_a0 h_v92 hinv27 s27 v92
  step as ⟨e_v94, he_v94⟩
  store_step with CtorSpec.eo__2b.construct s28 e_v94 (by rw [he_v94]; exact empty_args) hinv28 h64 as ⟨v94, s29, hinv29, h_v94⟩ growing hG carrying h_a1 h_a2 h_a3 h_v91 h_v93 dropping he_v94 hinv28 e_v94 s28
  store_step with Store.apply_rep s29 v94 a1 _ _ hinv29 h64 h_v94 h_a1 (by ns_tac) (by ns_tac) as ⟨v95, s30, hinv30, h_v95⟩ growing hG carrying h_a2 h_a3 h_v91 h_v93 dropping h_a1 h_v94 hinv29 s29 v94
  step as ⟨e_v96, he_v96⟩
  store_step with CtorSpec.eo__2b.construct s30 e_v96 (by rw [he_v96]; exact empty_args) hinv30 h64 as ⟨v96, s31, hinv31, h_v96⟩ growing hG carrying h_a2 h_a3 h_v91 h_v93 h_v95 dropping he_v96 hinv30 e_v96 s30
  store_step with Store.apply_rep s31 v96 a3 _ _ hinv31 h64 h_v96 h_a3 (by ns_tac) (by ns_tac) as ⟨v97, s32, hinv32, h_v97⟩ growing hG carrying h_a2 h_a3 h_v91 h_v93 h_v95 dropping h_v96 hinv31 s31 v96
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s32 0#u32 (0) (by scalar_tac) hinv32 h64 as ⟨v98, s33, hinv33, h_v98⟩ growing hG carrying h_a2 h_a3 h_v91 h_v93 h_v95 h_v97 dropping hinv32 s32
  store_step with Store.apply_rep s33 v97 v98 _ _ hinv33 h64 h_v97 h_v98 (by ns_tac) (by ns_tac) as ⟨v99, s34, hinv34, h_v99⟩ growing hG carrying h_a2 h_a3 h_v91 h_v93 h_v95 dropping h_v97 h_v98 hinv33 s33 v97 v98
  store_step with Store.apply_rep s34 v95 v99 _ _ hinv34 h64 h_v95 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s35, hinv35, h_v100⟩ growing hG carrying h_a2 h_a3 h_v91 h_v93 dropping h_v95 h_v99 hinv34 s34 v95 v99
  store_step with Store.apply_rep s35 v93 v100 _ _ hinv35 h64 h_v93 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s36, hinv36, h_v101⟩ growing hG carrying h_a2 h_a3 h_v91 dropping h_v100 h_v93 hinv35 s35 v100 v93
  step as ⟨e_v102, he_v102⟩
  store_step with CtorSpec.eo__2d.construct s36 e_v102 (by rw [he_v102]; exact empty_args) hinv36 h64 as ⟨v102, s37, hinv37, h_v102⟩ growing hG carrying h_a2 h_a3 h_v91 h_v101 dropping he_v102 hinv36 e_v102 s36
  store_step with Store.apply_rep s37 v102 a2 _ _ hinv37 h64 h_v102 h_a2 (by ns_tac) (by ns_tac) as ⟨v103, s38, hinv38, h_v103⟩ growing hG carrying h_a3 h_v91 h_v101 dropping h_a2 h_v102 hinv37 s37 v102
  store_step with Store.apply_rep s38 v103 a3 _ _ hinv38 h64 h_v103 h_a3 (by ns_tac) (by ns_tac) as ⟨v104, s39, hinv39, h_v104⟩ growing hG carrying h_v91 h_v101 dropping h_a3 h_v103 hinv38 s38 v103
  store_step with Store.apply_rep s39 v101 v104 _ _ hinv39 h64 h_v101 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s40, hinv40, h_v105⟩ growing hG carrying h_v91 dropping h_v101 h_v104 hinv39 s39 v101 v104
  store_step with Store.apply_rep s40 v91 v105 _ _ hinv40 h64 h_v91 h_v105 (by ns_tac) (by ns_tac) as ⟨v106, s41, hinv41, h_v106⟩ growing hG carrying dropping h_v105 h_v91 hinv40 s40 v105 v91
  case_done hinv41 hG with h_v106 in EoCases.__eo_prog_str_substr_combine4.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_a4 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50 hn_v53 hn_v54 hn_v56 hn_v57 hn_v60 hn_v61 hn_v63 hn_v64 hn_v68 hn_v69 hn_v72 hn_v73 hn_v75 hn_v76 hn_v78 hn_v79

/-- logos's `__eo_prog_str_substr_combine4` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dcombine4.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (x_a6 : _) (x_a7 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) (hw_a6 : Valid.valid x_a6) (hw_a7 : Valid.valid x_a7) :
    __eo_prog_str_substr_combine4 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else if x_a4 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_combine4.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 x_a6 x_a7] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_combine4
  unfold EoCases.__eo_prog_str_substr_combine4.case_0
  logos_eq

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

theorem case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_substr_concat1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_substr_concat1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v6 h_v7 dropping h_a4 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_same v14 a2 with h_v14 h_a2 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 h_v11 dropping h_v13 h_v14 h_v15 hinv2 s2 v13 v14 v15
  pat_same v11 v16 with h_v11 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a5 h_v4 dropping h_v11 h_v16 hinv3 s3 v11 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v19, x_v19, h_v19⟩ else hinv4 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v19 as ⟨v21, v22, x_v21, x_v22, h_v21, h_v22, hn_v21, hn_v22⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v21 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v24 h_v25 dropping h_a5 h_v17 h_v19 h_v21 h_v4 he_v26 hinv4 e_v26 s4 v17 v19 v21 v4
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v25 as ⟨v28, v29, x_v28, x_v29, h_v28, h_v29, hn_v28, hn_v29⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v28 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3e_3d.construct s5 e_v33 (by rw [he_v33]; exact empty_args) hinv5 h64 as ⟨v33, s6, hinv6, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v29 h_v31 h_v32 dropping h_v24 h_v25 h_v26 h_v28 he_v33 hinv5 e_v33 s5 v24 v25 v26 v28
  pat_same v31 v33 with h_v31 h_v33 using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v32 as ⟨v35, v36, x_v35, x_v36, h_v35, h_v36, hn_v35, hn_v36⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v29 h_v35 h_v36 dropping h_v31 h_v32 h_v33 he_v37 hinv6 e_v37 s6 v31 v32 v33
  pat_same v35 v37 with h_v35 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_same v36 a0 with h_v36 h_a0 using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v29 as ⟨v39, v40, x_v39, x_v40, h_v39, h_v40, hn_v39, hn_v40⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v39 as ⟨v42, v43, x_v42, x_v43, h_v42, h_v43, hn_v42, hn_v43⟩ using hinv7 else hinv7 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__2b.construct s7 e_v44 (by rw [he_v44]; exact empty_args) hinv7 h64 as ⟨v44, s8, hinv8, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v40 h_v42 h_v43 dropping h_v29 h_v35 h_v36 h_v37 h_v39 he_v44 hinv7 e_v44 s7 v29 v35 v36 v37 v39
  pat_same v42 v44 with h_v42 h_v44 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_same v43 a2 with h_v43 h_a2 using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v40 as ⟨v46, v47, x_v46, x_v47, h_v46, h_v47, hn_v46, hn_v47⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_unapply h_v46 as ⟨v49, v50, x_v49, x_v50, h_v49, h_v50, hn_v49, hn_v50⟩ using hinv8 else hinv8 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v51, he_v51⟩
  store_step with CtorSpec.eo__2b.construct s8 e_v51 (by rw [he_v51]; exact empty_args) hinv8 h64 as ⟨v51, s9, hinv9, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v47 h_v49 h_v50 dropping h_v40 h_v42 h_v43 h_v44 h_v46 he_v51 hinv8 e_v51 s8 v40 v42 v43 v44 v46
  pat_same v49 v51 with h_v49 h_v51 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  pat_same v50 a3 with h_v50 h_a3 using hinv9 else hinv9 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v52, s10, hinv10, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 h_v47 dropping h_v49 h_v50 h_v51 hinv9 s9 v49 v50 v51
  pat_same v47 v52 with h_v47 h_v52 using hinv10 else hinv10 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v53, s11, hinv11, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v22 dropping h_v47 h_v52 hinv10 s10 v47 v52
  pat_same v22 v53 with h_v22 h_v53 using hinv11 else hinv11 hG in EoCases.__eo_prog_str_substr_concat1.case_0
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo__3d.construct s11 e_v54 (by rw [he_v54]; exact empty_args) hinv11 h64 as ⟨v54, s12, hinv12, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v22 h_v53 he_v54 hinv11 e_v54 s11 v22 v53
  step as ⟨e_v55, he_v55⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s12 e_v55 (by rw [he_v55]; exact empty_args) hinv12 h64 as ⟨v55, s13, hinv13, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v54 dropping he_v55 hinv12 e_v55 s12
  step as ⟨e_v56, he_v56⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s13 e_v56 (by rw [he_v56]; exact empty_args) hinv13 h64 as ⟨v56, s14, hinv14, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v54 h_v55 dropping he_v56 hinv13 e_v56 s13
  store_step with Store.apply_rep s14 v56 a0 _ _ hinv14 h64 h_v56 h_a0 (by ns_tac) (by ns_tac) as ⟨v57, s15, hinv15, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v54 h_v55 dropping h_v56 hinv14 s14 v56
  store_step with Store.apply_rep s15 v57 a1 _ _ hinv15 h64 h_v57 h_a1 (by ns_tac) (by ns_tac) as ⟨v58, s16, hinv16, h_v58⟩ growing hG carrying h_a0 h_a2 h_a3 h_v54 h_v55 dropping h_a1 h_v57 hinv15 s15 v57
  store_step with Store.apply_rep s16 v55 v58 _ _ hinv16 h64 h_v55 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s17, hinv17, h_v59⟩ growing hG carrying h_a0 h_a2 h_a3 h_v54 dropping h_v55 h_v58 hinv16 s16 v55 v58
  store_step with Store.apply_rep s17 v59 a2 _ _ hinv17 h64 h_v59 h_a2 (by ns_tac) (by ns_tac) as ⟨v60, s18, hinv18, h_v60⟩ growing hG carrying h_a0 h_a2 h_a3 h_v54 dropping h_v59 hinv17 s17 v59
  store_step with Store.apply_rep s18 v60 a3 _ _ hinv18 h64 h_v60 h_a3 (by ns_tac) (by ns_tac) as ⟨v61, s19, hinv19, h_v61⟩ growing hG carrying h_a0 h_a2 h_a3 h_v54 dropping h_v60 hinv18 s18 v60
  store_step with Store.apply_rep s19 v54 v61 _ _ hinv19 h64 h_v54 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s20, hinv20, h_v62⟩ growing hG carrying h_a0 h_a2 h_a3 dropping h_v54 h_v61 hinv19 s19 v54 v61
  step as ⟨e_v63, he_v63⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s20 e_v63 (by rw [he_v63]; exact empty_args) hinv20 h64 as ⟨v63, s21, hinv21, h_v63⟩ growing hG carrying h_a0 h_a2 h_a3 h_v62 dropping he_v63 hinv20 e_v63 s20
  store_step with Store.apply_rep s21 v63 a0 _ _ hinv21 h64 h_v63 h_a0 (by ns_tac) (by ns_tac) as ⟨v64, s22, hinv22, h_v64⟩ growing hG carrying h_a2 h_a3 h_v62 dropping h_a0 h_v63 hinv21 s21 v63
  store_step with Store.apply_rep s22 v64 a2 _ _ hinv22 h64 h_v64 h_a2 (by ns_tac) (by ns_tac) as ⟨v65, s23, hinv23, h_v65⟩ growing hG carrying h_a3 h_v62 dropping h_a2 h_v64 hinv22 s22 v64
  store_step with Store.apply_rep s23 v65 a3 _ _ hinv23 h64 h_v65 h_a3 (by ns_tac) (by ns_tac) as ⟨v66, s24, hinv24, h_v66⟩ growing hG carrying h_v62 dropping h_a3 h_v65 hinv23 s23 v65
  store_step with Store.apply_rep s24 v62 v66 _ _ hinv24 h64 h_v62 h_v66 (by ns_tac) (by ns_tac) as ⟨v67, s25, hinv25, h_v67⟩ growing hG carrying dropping h_v62 h_v66 hinv24 s24 v62 v66
  case_done hinv25 hG with h_v67 in EoCases.__eo_prog_str_substr_concat1.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v21 hn_v22 hn_v24 hn_v25 hn_v28 hn_v29 hn_v31 hn_v32 hn_v35 hn_v36 hn_v39 hn_v40 hn_v42 hn_v43 hn_v46 hn_v47 hn_v49 hn_v50

/-- logos's `__eo_prog_str_substr_concat1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_substr_concat1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_substr_concat1.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_substr_concat1
  unfold EoCases.__eo_prog_str_substr_concat1.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_substr_concat1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_substr_concat1.case_0

theorem eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_substr_concat1 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dsubstr_2dconcat1_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
