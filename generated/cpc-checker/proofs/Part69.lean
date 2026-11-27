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

set_option maxHeartbeats 4000000 in
theorem case_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_re_concat_merge.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_re_concat_merge.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping he_v0 e_v0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping he_v1 hinv1 e_v1 s1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 dropping he_v3 hinv3 e_v3 s3
  store_step with Store.apply_rep s4 v3 a1 _ _ hinv4 h64 h_v3 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 dropping h_v3 hinv4 s4 v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v2 h_v4 hinv5 s5 v2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v5 dropping he_v6 hinv6 e_v6 s6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s7 e_v7 (by rw [he_v7]; exact empty_args) hinv7 h64 as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v5 h_v6 dropping he_v7 hinv7 e_v7 s7
  store_step with Store.apply_rep s8 v7 a2 _ _ hinv8 h64 h_v7 h_a2 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v5 h_v6 dropping h_v7 hinv8 s8 v7
  store_step with Store.apply_rep s9 v6 v8 _ _ hinv9 h64 h_v6 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v5 dropping h_v6 h_v8 hinv9 s9 v6 v8
  store_step with Store.apply_rep s10 v9 a3 _ _ hinv10 h64 h_v9 h_a3 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v5 dropping h_v9 hinv10 s10 v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 dropping h_v10 h_v5 hinv11 s11 v10 v5
  step as ⟨e_v12, he_v12⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s12 e_v12 (by rw [he_v12]; rfl) h_v1 h_a0 h_v11 hinv12 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 dropping h_v1 h_v11 he_v12 hinv12 e_v12 s12 v1 v11
  store_step with Store.apply_mk_rep s13 v0 v12 _ _ hinv13 h64 h_v0 h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 dropping h_v0 h_v12 hinv13 s13 v0 v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v13 dropping he_v14 hinv14 e_v14 s14
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v13 h_v14 dropping he_v15 hinv15 e_v15 s15
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v13 h_v14 h_v15 dropping he_v16 hinv16 e_v16 s16
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v13 h_v14 h_v15 h_v16 dropping he_v17 hinv17 e_v17 s17
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s18 e_v18 (by rw [he_v18]; exact empty_args) hinv18 h64 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 dropping he_v18 hinv18 e_v18 s18
  store_step with Store.apply_rep s19 v18 a1 _ _ hinv19 h64 h_v18 h_a1 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a2 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 dropping h_a1 h_v18 hinv19 s19 v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s20 e_v20 (by rw [he_v20]; exact empty_args) hinv20 h64 as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a2 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 dropping he_v20 hinv20 e_v20 s20
  store_step with Store.apply_rep s21 v20 a2 _ _ hinv21 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 dropping h_a2 h_v20 hinv21 s21 v20
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s22 _ _ rfl hinv22 h64 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 h_v21 dropping hinv22 s22
  store_step with Store.apply_rep s23 v21 v22 _ _ hinv23 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 h_v19 dropping h_v21 h_v22 hinv23 s23 v21 v22
  store_step with Store.apply_rep s24 v19 v23 _ _ hinv24 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a3 h_v13 h_v14 h_v15 h_v16 h_v17 dropping h_v19 h_v23 hinv24 s24 v19 v23
  store_step with Store.apply_rep s25 v17 v24 _ _ hinv25 h64 h_v17 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a3 h_v13 h_v14 h_v15 h_v16 dropping h_v17 h_v24 hinv25 s25 v17 v24
  store_step with Store.apply_rep s26 v16 v25 _ _ hinv26 h64 h_v16 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a3 h_v13 h_v14 h_v15 dropping h_v16 h_v25 hinv26 s26 v16 v25
  store_step with Store.apply_rep s27 v26 a3 _ _ hinv27 h64 h_v26 h_a3 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_a0 h_v13 h_v14 h_v15 dropping h_a3 h_v26 hinv27 s27 v26
  step as ⟨e_v28, he_v28⟩
  store_step with Store.builtin_spec_list_concat n ih.eo__24eo_5fis_5flist_5fnil s28 e_v28 (by rw [he_v28]; rfl) h_v15 h_a0 h_v27 hinv28 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_unique_nil_eo_re_2e_2b_2b as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying h_v13 h_v14 dropping h_a0 h_v15 h_v27 he_v28 hinv28 e_v28 s28 v15 v27
  step as ⟨e_v29, he_v29⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s29 e_v29 (by rw [he_v29]; rfl) h_v14 h_v28 hinv29 h64 (hG.rem hrem) op_not_left_eo_re_2e_2b_2b op_nil_apply_eo_re_2e_2b_2b as ⟨v29, s30, hinv30, h_v29⟩ growing hG carrying h_v13 dropping h_v14 h_v28 he_v29 hinv29 e_v29 s29 v14 v28
  store_step with Store.apply_mk_rep s30 v13 v29 _ _ hinv30 h64 h_v13 h_v29 as ⟨v30, s31, hinv31, h_v30⟩ growing hG carrying dropping h_v13 h_v29 hinv30 s30 v13 v29
  case_done hinv31 hG with h_v30 in EoCases.__eo_prog_re_concat_merge.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

set_option maxHeartbeats 4000000 in
/-- logos's `__eo_prog_re_concat_merge` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fre_2dconcat_2dmerge.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_re_concat_merge x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_re_concat_merge.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_re_concat_merge
  unfold EoCases.__eo_prog_re_concat_merge.case_0
  logos_eq

set_option maxHeartbeats 4000000 in
theorem body_eo__24eo_5fprog_5fre_2dconcat_2dmerge_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fre_2dconcat_2dmerge s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_re_concat_merge x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fre_2dconcat_2dmerge.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fre_2dconcat_2dmerge
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fre_2dconcat_2dmerge_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_re_concat_merge.case_0

set_option maxHeartbeats 4000000 in
theorem eo__24eo_5fprog_5fre_2dconcat_2dmerge_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fre_2dconcat_2dmerge.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fre_2dconcat_2dmerge
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fre_2dconcat_2dmerge s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_re_concat_merge x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fre_2dconcat_2dmerge_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
