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

set_option maxHeartbeats 20000000 in
theorem case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_concat_star_nullable1.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_concat_star_nullable1.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v6 h_v7 dropping h_a3 h_v1 h_v3 he_v8 e_v8 v1 v3
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2ein_5fre.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v13 h_v14 dropping h_v10 h_v6 h_v7 h_v8 he_v15 hinv1 e_v15 s1 v10 v6 v7 v8
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 h_v11 h_v14 dropping h_v13 h_v15 hinv2 s2 v13 v15
  pat_same v14 v16 with h_v14 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v4 dropping h_v11 h_v14 h_v16 hinv3 s3 v11 v14 v16
  pat_same v4 v17 with h_v4 h_v17 using hinv4 else hinv4 hG in EoCases.__eo_prog_re_concat_star_nullable1.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v18 (by rw [he_v18]; exact empty_args) hinv4 h64 as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 dropping h_v17 h_v4 he_v18 hinv4 e_v18 s4 v17 v4
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s5 e_v19 (by rw [he_v19]; exact empty_args) hinv5 h64 as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 dropping he_v19 hinv5 e_v19 s5
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s6 e_v20 (by rw [he_v20]; exact empty_args) hinv6 h64 as ⟨v20, s7, hinv7, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v19 dropping he_v20 hinv6 e_v20 s6
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s7 e_v21 (by rw [he_v21]; exact empty_args) hinv7 h64 as ⟨v21, s8, hinv8, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v19 h_v20 dropping he_v21 hinv7 e_v21 s7
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s8 e_v22 (by rw [he_v22]; exact empty_args) hinv8 h64 as ⟨v22, s9, hinv9, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v19 h_v20 h_v21 dropping he_v22 hinv8 e_v22 s8
  store_step with Store.apply_rep s9 v21 v22 _ _ hinv9 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s10, hinv10, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v19 h_v20 dropping h_v21 h_v22 hinv9 s9 v21 v22
  store_step with Store.apply_rep s10 v20 v23 _ _ hinv10 h64 h_v20 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s11, hinv11, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v19 dropping h_v20 h_v23 hinv10 s10 v20 v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s11 e_v25 (by rw [he_v25]; exact empty_args) hinv11 h64 as ⟨v25, s12, hinv12, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v18 h_v19 h_v24 dropping he_v25 hinv11 e_v25 s11
  store_step with Store.apply_rep s12 v25 a1 _ _ hinv12 h64 h_v25 h_a1 (by ns_tac) (by ns_tac) as ⟨v26, s13, hinv13, h_v26⟩ growing hG carrying h_a0 h_a2 h_v18 h_v19 h_v24 dropping h_a1 h_v25 hinv12 s12 v25
  store_step with Store.apply_rep s13 v26 a2 _ _ hinv13 h64 h_v26 h_a2 (by ns_tac) (by ns_tac) as ⟨v27, s14, hinv14, h_v27⟩ growing hG carrying h_a0 h_a2 h_v18 h_v19 h_v24 dropping h_v26 hinv13 s13 v26
  store_step with Store.apply_rep s14 v24 v27 _ _ hinv14 h64 h_v24 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s15, hinv15, h_v28⟩ growing hG carrying h_a0 h_a2 h_v18 h_v19 dropping h_v24 h_v27 hinv14 s14 v24 v27
  step as ⟨e_v29, he_v29⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s15 e_v29 (by rw [he_v29]; rfl) h_v19 h_a0 h_v28 hinv15 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v29, s16, hinv16, h_v29⟩ growing hG carrying h_a0 h_a2 h_v18 dropping h_v19 h_v28 he_v29 hinv15 e_v29 s15 v19 v28
  store_step with Store.apply_mk_rep s16 v18 v29 _ _ hinv16 h64 h_v18 h_v29 as ⟨v30, s17, hinv17, h_v30⟩ growing hG carrying h_a0 h_a2 dropping h_v18 h_v29 hinv16 s16 v18 v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s17 e_v31 (by rw [he_v31]; exact empty_args) hinv17 h64 as ⟨v31, s18, hinv18, h_v31⟩ growing hG carrying h_a0 h_a2 h_v30 dropping he_v31 hinv17 e_v31 s17
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s18 e_v32 (by rw [he_v32]; exact empty_args) hinv18 h64 as ⟨v32, s19, hinv19, h_v32⟩ growing hG carrying h_a0 h_a2 h_v30 h_v31 dropping he_v32 hinv18 e_v32 s18
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s19 e_v33 (by rw [he_v33]; exact empty_args) hinv19 h64 as ⟨v33, s20, hinv20, h_v33⟩ growing hG carrying h_a0 h_a2 h_v30 h_v31 h_v32 dropping he_v33 hinv19 e_v33 s19
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_re_2e_2a.construct s20 e_v34 (by rw [he_v34]; exact empty_args) hinv20 h64 as ⟨v34, s21, hinv21, h_v34⟩ growing hG carrying h_a0 h_a2 h_v30 h_v31 h_v32 h_v33 dropping he_v34 hinv20 e_v34 s20
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_re_2eallchar.construct s21 e_v35 (by rw [he_v35]; exact empty_args) hinv21 h64 as ⟨v35, s22, hinv22, h_v35⟩ growing hG carrying h_a0 h_a2 h_v30 h_v31 h_v32 h_v33 h_v34 dropping he_v35 hinv21 e_v35 s21
  store_step with Store.apply_rep s22 v34 v35 _ _ hinv22 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s23, hinv23, h_v36⟩ growing hG carrying h_a0 h_a2 h_v30 h_v31 h_v32 h_v33 dropping h_v34 h_v35 hinv22 s22 v34 v35
  store_step with Store.apply_rep s23 v33 v36 _ _ hinv23 h64 h_v33 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s24, hinv24, h_v37⟩ growing hG carrying h_a0 h_a2 h_v30 h_v31 h_v32 dropping h_v33 h_v36 hinv23 s23 v33 v36
  store_step with Store.apply_rep s24 v37 a2 _ _ hinv24 h64 h_v37 h_a2 (by ns_tac) (by ns_tac) as ⟨v38, s25, hinv25, h_v38⟩ growing hG carrying h_a0 h_v30 h_v31 h_v32 dropping h_a2 h_v37 hinv24 s24 v37
  step as ⟨e_v39, he_v39⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s25 e_v39 (by rw [he_v39]; rfl) h_v32 h_a0 h_v38 hinv25 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v39, s26, hinv26, h_v39⟩ growing hG carrying h_v30 h_v31 dropping h_a0 h_v32 h_v38 he_v39 hinv25 e_v39 s25 v32 v38
  step as ⟨e_v40, he_v40⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s26 e_v40 (by rw [he_v40]; rfl) h_v31 h_v39 hinv26 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_nil_apply_eo_re_2e_2b_2b as ⟨v40, s27, hinv27, h_v40⟩ growing hG carrying h_v30 dropping h_v31 h_v39 he_v40 hinv26 e_v40 s26 v31 v39
  store_step with Store.apply_mk_rep s27 v30 v40 _ _ hinv27 h64 h_v30 h_v40 as ⟨v41, s28, hinv28, h_v41⟩ growing hG carrying dropping h_v30 h_v40 hinv27 s27 v30 v40
  case_done hinv28 hG with h_v41 in EoCases.__eo_prog_re_concat_star_nullable1.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

set_option maxHeartbeats 20000000 in
/-- logos's `__eo_prog_re_concat_star_nullable1` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_re_concat_star_nullable1 x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_concat_star_nullable1.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_concat_star_nullable1
  unfold EoCases.__eo_prog_re_concat_star_nullable1.case_0
  logos_eq

set_option maxHeartbeats 20000000 in
theorem body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1 s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_star_nullable1 x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_re_concat_star_nullable1.case_0

set_option maxHeartbeats 20000000 in
theorem eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1 s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_re_concat_star_nullable1 x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dconcat_2dstar_2dnullable1_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
