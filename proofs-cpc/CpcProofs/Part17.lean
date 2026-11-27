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

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_concat.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_concat.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat more_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat more_1_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v17 a1 _ _ hinv18 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v18 a2 _ _ hinv19 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s20 e_v20 (by rw [he_v20]; rfl) h_v16 h_v19 hinv20 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s21 v15 v20 _ _ hinv21 h64 h_v15 h_v20 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_mk_rep s22 v14 v21 _ _ hinv22 h64 h_v14 h_v21 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s23 _ _ rfl hinv23 h64 as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_mk_rep s24 v22 v23 _ _ hinv24 h64 h_v22 h_v23 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_mk_rep s25 v13 v24 _ _ hinv25 h64 h_v13 h_v24 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_mk_rep s26 v9 v25 _ _ hinv26 h64 h_v9 h_v25 as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  case_done hinv27 hG with h_v26 in EoCases.__eo_prog_str_to_lower_concat.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_str_to_lower_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_to_lower_concat x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_concat.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_concat
  unfold EoCases.__eo_prog_str_to_lower_concat.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_concat x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_to_lower_concat.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_concat x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dconcat_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_from_int.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_from_int.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_from_int.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_from_int` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_from_int x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_from_int.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_from_int
  unfold EoCases.__eo_prog_str_to_lower_from_int.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_from_int x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_from_int.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_from_int x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dfrom_2dint_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_idem.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_idem.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_idem.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_idem` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_idem x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_idem.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_idem
  unfold EoCases.__eo_prog_str_to_lower_idem.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_idem x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_idem.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2didem.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2didem
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_idem x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2didem_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_len.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_len.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_len.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_len x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_len.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_len
  unfold EoCases.__eo_prog_str_to_lower_len.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_len x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_len.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_len x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dlen_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_lower_upper.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_lower_upper.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_lower_upper.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_lower_upper` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_lower_upper x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_lower_upper.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_lower_upper
  unfold EoCases.__eo_prog_str_to_lower_upper.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_lower_upper x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_lower_upper.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_lower_upper x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dlower_2dupper_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_concat.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_concat.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat more_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat more_1_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s4 e_v4 (by rw [he_v4]; exact empty_args) hinv4 h64 as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v4 a1 _ _ hinv5 h64 h_v4 h_a1 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v5 a2 _ _ hinv6 h64 h_v5 h_a2 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v3 v6 _ _ hinv7 h64 h_v3 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v0 v8 _ _ hinv9 h64 h_v0 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s15 e_v15 (by rw [he_v15]; exact empty_args) hinv15 h64 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v16 (by rw [he_v16]; exact empty_args) hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s17 e_v17 (by rw [he_v17]; exact empty_args) hinv17 h64 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v17 a1 _ _ hinv18 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s19 v18 a2 _ _ hinv19 h64 h_v18 h_a2 (by ns_tac) (by ns_tac) as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s20 e_v20 (by rw [he_v20]; rfl) h_v16 h_v19 hinv20 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s21 v15 v20 _ _ hinv21 h64 h_v15 h_v20 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_mk_rep s22 v14 v21 _ _ hinv22 h64 h_v14 h_v21 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s23 _ _ rfl hinv23 h64 as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_mk_rep s24 v22 v23 _ _ hinv24 h64 h_v22 h_v23 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_mk_rep s25 v13 v24 _ _ hinv25 h64 h_v13 h_v24 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_mk_rep s26 v9 v25 _ _ hinv26 h64 h_v9 h_v25 as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  case_done hinv27 hG with h_v26 in EoCases.__eo_prog_str_to_upper_concat.case_0 using hn_a0 hn_a1 hn_a2

/-- logos's `__eo_prog_str_to_upper_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_str_to_upper_concat x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_concat.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_concat
  unfold EoCases.__eo_prog_str_to_upper_concat.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_concat x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_to_upper_concat.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_concat x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dconcat_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_from_int.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_from_int.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2efrom_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_from_int.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_from_int` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_from_int x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_from_int.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_from_int
  unfold EoCases.__eo_prog_str_to_upper_from_int.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_from_int x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_from_int.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_from_int x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dfrom_2dint_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_idem.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_idem.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_idem.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_idem` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_idem x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_idem.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_idem
  unfold EoCases.__eo_prog_str_to_upper_idem.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_idem x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_idem.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2didem.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2didem
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_idem x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2didem_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_len.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_len.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2elen.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_len.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_len` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_len x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_len.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_len
  unfold EoCases.__eo_prog_str_to_upper_len.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_len x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_len.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_len x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlen_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_to_upper_lower.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_to_upper_lower.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5flower.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_str_2eto_5fupper.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv9 hG with h_v8 in EoCases.__eo_prog_str_to_upper_lower.case_0 using hn_a0

/-- logos's `__eo_prog_str_to_upper_lower` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_str_to_upper_lower x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_to_upper_lower.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_to_upper_lower
  unfold EoCases.__eo_prog_str_to_upper_lower.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_to_upper_lower x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_str_to_upper_lower.case_0

theorem eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_str_to_upper_lower x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dto_2dupper_2dlower_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_concat_fit0.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_concat_fit0.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 more_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 more_1_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a5 as ⟨v11, x_v11, h_v11⟩ else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v11 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v18 (by rw [he_v18]; exact empty_args) hinv2 h64 as ⟨v18, s3, hinv3, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17
  pat_same v16 v18 with h_v16 h_v18 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_same v21 a0 with h_v21 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_unapply h_v14 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  pat_same v25 a3 with h_v25 h_a3 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_concat_fit0.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v29 (by rw [he_v29]; exact empty_args) hinv7 h64 as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s8 v29 a0 _ _ hinv8 h64 h_v29 h_a0 (by ns_tac) (by ns_tac) as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s9 v30 a1 _ _ hinv9 h64 h_v30 h_a1 (by ns_tac) (by ns_tac) as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s10 v28 v31 _ _ hinv10 h64 h_v28 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s11, hinv11, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s11 v32 a2 _ _ hinv11 h64 h_v32 h_a2 (by ns_tac) (by ns_tac) as ⟨v33, s12, hinv12, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s12 v33 a3 _ _ hinv12 h64 h_v33 h_a3 (by ns_tac) (by ns_tac) as ⟨v34, s13, hinv13, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s13 v27 v34 _ _ hinv13 h64 h_v27 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s14, hinv14, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s14 e_v36 (by rw [he_v36]; exact empty_args) hinv14 h64 as ⟨v36, s15, hinv15, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s15 e_v37 (by rw [he_v37]; exact empty_args) hinv15 h64 as ⟨v37, s16, hinv16, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s16 v37 a3 _ _ hinv16 h64 h_v37 h_a3 (by ns_tac) (by ns_tac) as ⟨v38, s17, hinv17, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s17 v38 a1 _ _ hinv17 h64 h_v38 h_a1 (by ns_tac) (by ns_tac) as ⟨v39, s18, hinv18, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s18 e_v40 (by rw [he_v40]; rfl) h_v36 h_v39 hinv18 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v40, s19, hinv19, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_mk_rep s19 v35 v40 _ _ hinv19 h64 h_v35 h_v40 as ⟨v41, s20, hinv20, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  case_done hinv20 hG with h_v41 in EoCases.__eo_prog_str_update_concat_fit0.case_0 using hn_a0 hn_a1 hn_a2 hn_a3 hn_v3 hn_v4 hn_v6 hn_v7 hn_v13 hn_v14 hn_v16 hn_v17 hn_v20 hn_v21 hn_v24 hn_v25

/-- logos's `__eo_prog_str_update_concat_fit0` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) (hw_a5 : Valid.valid x_a5) :
    __eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_concat_fit0.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_concat_fit0
  unfold EoCases.__eo_prog_str_update_concat_fit0.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 a5 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (x_a5 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (h_a5 : Represents.rep s a5 x_a5) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s a0 a1 a2 a3 a4 a5 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4) (by valid_tac hinv h_a5)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec n ih s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 using hn_a0 hn_a1 hn_a2 hn_a3
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hn_a3 hc0 in EoCases.__eo_prog_str_update_concat_fit0.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0.Spec n := by
  intro s a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 h_a5
  unfold eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0 s1 a0 a1 a2 a3 a4 a5) (fun s' t => Represents.rep s' t (__eo_prog_str_update_concat_fit0 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0_spec m (ih m hm) s1 a0 a1 a2 a3 a4 a5 x_a0 x_a1 x_a2 x_a3 x_a4 x_a5 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) (by congr_one h_a5 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_fit.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_fit.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit more_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit more_1_eo__24eo_5fprog_5fstr_2dupdate_2dfit
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_same v7 a1 with h_v7 h_a1 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_fit.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v11, x_v11, h_v11⟩ else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v11 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v18 (by rw [he_v18]; exact empty_args) hinv2 h64 as ⟨v18, s3, hinv3, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17
  pat_same v16 v18 with h_v16 h_v18 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_same v21 a0 with h_v21 h_a0 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_unapply h_v14 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2elen.construct s4 e_v26 (by rw [he_v26]; exact empty_args) hinv4 h64 as ⟨v26, s5, hinv5, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25
  pat_same v24 v26 with h_v24 h_v26 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_fit.case_0
  pat_same v25 a2 with h_v25 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_fit.case_0
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v27 (by rw [he_v27]; exact empty_args) hinv5 h64 as ⟨v27, s6, hinv6, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v28 (by rw [he_v28]; exact empty_args) hinv6 h64 as ⟨v28, s7, hinv7, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s7 v28 a0 _ _ hinv7 h64 h_v28 h_a0 (by ns_tac) (by ns_tac) as ⟨v29, s8, hinv8, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s8 v29 a1 _ _ hinv8 h64 h_v29 h_a1 (by ns_tac) (by ns_tac) as ⟨v30, s9, hinv9, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s9 v30 a2 _ _ hinv9 h64 h_v30 h_a2 (by ns_tac) (by ns_tac) as ⟨v31, s10, hinv10, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s10 v27 v31 _ _ hinv10 h64 h_v27 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s11, hinv11, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s11 v32 a2 _ _ hinv11 h64 h_v32 h_a2 (by ns_tac) (by ns_tac) as ⟨v33, s12, hinv12, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  case_done hinv12 hG with h_v33 in EoCases.__eo_prog_str_update_fit.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v13 hn_v14 hn_v16 hn_v17 hn_v20 hn_v21 hn_v24 hn_v25

/-- logos's `__eo_prog_str_update_fit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2dfit.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_fit.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_fit
  unfold EoCases.__eo_prog_str_update_fit.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2dfit s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2dfit.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2dfit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_update_fit.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2dfit.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fstr_2dupdate_2dfit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2dfit s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_str_update_fit x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2dfit_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_oob.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_oob.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob more_0_eo__24eo_5fprog_5fstr_2dupdate_2doob more_1_eo__24eo_5fprog_5fstr_2dupdate_2doob
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_str_2elen.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v11 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2esubstr.construct s2 e_v22 (by rw [he_v22]; exact empty_args) hinv2 h64 as ⟨v22, s3, hinv3, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_same v21 a0 with h_v21 h_a0 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_oob.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_oob.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v23, s4, hinv4, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22
  pat_same v15 v23 with h_v15 h_v23 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_oob.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s4 0#u32 (0) (by scalar_tac) hinv4 h64 as ⟨v24, s5, hinv5, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23
  pat_same v4 v24 with h_v4 h_v24 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_oob.case_0
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v25 (by rw [he_v25]; exact empty_args) hinv5 h64 as ⟨v25, s6, hinv6, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v26 (by rw [he_v26]; exact empty_args) hinv6 h64 as ⟨v26, s7, hinv7, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s7 v26 a0 _ _ hinv7 h64 h_v26 h_a0 (by ns_tac) (by ns_tac) as ⟨v27, s8, hinv8, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s8 v27 a1 _ _ hinv8 h64 h_v27 h_a1 (by ns_tac) (by ns_tac) as ⟨v28, s9, hinv9, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s9 v28 a2 _ _ hinv9 h64 h_v28 h_a2 (by ns_tac) (by ns_tac) as ⟨v29, s10, hinv10, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s10 v25 v29 _ _ hinv10 h64 h_v25 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s11, hinv11, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s11 v30 a0 _ _ hinv11 h64 h_v30 h_a0 (by ns_tac) (by ns_tac) as ⟨v31, s12, hinv12, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  case_done hinv12 hG with h_v31 in EoCases.__eo_prog_str_update_oob.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15 hn_v17 hn_v18 hn_v20 hn_v21

/-- logos's `__eo_prog_str_update_oob` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2doob.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_oob.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_oob
  unfold EoCases.__eo_prog_str_update_oob.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2doob s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2doob.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2doob
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_update_oob.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2doob_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2doob.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dupdate_2doob
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2doob s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_update_oob x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2doob_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_str_update_rev.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_str_update_rev.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev more_0_eo__24eo_5fprog_5fstr_2dupdate_2drev more_1_eo__24eo_5fprog_5fstr_2dupdate_2drev more_2_eo__24eo_5fprog_5fstr_2dupdate_2drev
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_unapply h_v14 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_rev.case_0
  pat_same v18 a2 with h_v18 h_a2 using hinv3 else hinv3 hG in EoCases.__eo_prog_str_update_rev.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 1#u32 (1) (by scalar_tac) hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v11 v20 with h_v11 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_str_update_rev.case_0
  store_step with Store.literal_boolean_spec s4 true hinv4 h64 as ⟨v21, s5, hinv5, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20
  pat_same v4 v21 with h_v4 h_v21 using hinv5 else hinv5 hG in EoCases.__eo_prog_str_update_rev.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3d.construct s5 e_v22 (by rw [he_v22]; exact empty_args) hinv5 h64 as ⟨v22, s6, hinv6, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s6 e_v23 (by rw [he_v23]; exact empty_args) hinv6 h64 as ⟨v23, s7, hinv7, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_str_2erev.construct s7 e_v24 (by rw [he_v24]; exact empty_args) hinv7 h64 as ⟨v24, s8, hinv8, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s8 v24 a0 _ _ hinv8 h64 h_v24 h_a0 (by ns_tac) (by ns_tac) as ⟨v25, s9, hinv9, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s9 v23 v25 _ _ hinv9 h64 h_v23 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s10, hinv10, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s10 v26 a1 _ _ hinv10 h64 h_v26 h_a1 (by ns_tac) (by ns_tac) as ⟨v27, s11, hinv11, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s11 v27 a2 _ _ hinv11 h64 h_v27 h_a2 (by ns_tac) (by ns_tac) as ⟨v28, s12, hinv12, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s12 v22 v28 _ _ hinv12 h64 h_v22 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s13, hinv13, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_str_2erev.construct s13 e_v30 (by rw [he_v30]; exact empty_args) hinv13 h64 as ⟨v30, s14, hinv14, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_str_2eupdate.construct s14 e_v31 (by rw [he_v31]; exact empty_args) hinv14 h64 as ⟨v31, s15, hinv15, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s15 v31 a0 _ _ hinv15 h64 h_v31 h_a0 (by ns_tac) (by ns_tac) as ⟨v32, s16, hinv16, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__2d.construct s16 e_v33 (by rw [he_v33]; exact empty_args) hinv16 h64 as ⟨v33, s17, hinv17, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_str_2elen.construct s17 e_v34 (by rw [he_v34]; exact empty_args) hinv17 h64 as ⟨v34, s18, hinv18, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s18 v34 a0 _ _ hinv18 h64 h_v34 h_a0 (by ns_tac) (by ns_tac) as ⟨v35, s19, hinv19, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s19 v33 v35 _ _ hinv19 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s20, hinv20, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__2b.construct s20 e_v37 (by rw [he_v37]; exact empty_args) hinv20 h64 as ⟨v37, s21, hinv21, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s21 v37 a1 _ _ hinv21 h64 h_v37 h_a1 (by ns_tac) (by ns_tac) as ⟨v38, s22, hinv22, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__2b.construct s22 e_v39 (by rw [he_v39]; exact empty_args) hinv22 h64 as ⟨v39, s23, hinv23, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s23 1#u32 (1) (by scalar_tac) hinv23 h64 as ⟨v40, s24, hinv24, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s24 v39 v40 _ _ hinv24 h64 h_v39 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s25, hinv25, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v42, s26, hinv26, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s26 v41 v42 _ _ hinv26 h64 h_v41 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s27, hinv27, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s27 v38 v43 _ _ hinv27 h64 h_v38 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s28, hinv28, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s28 v36 v44 _ _ hinv28 h64 h_v36 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s29, hinv29, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s29 v32 v45 _ _ hinv29 h64 h_v32 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s30, hinv30, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s30 v46 a2 _ _ hinv30 h64 h_v46 h_a2 (by ns_tac) (by ns_tac) as ⟨v47, s31, hinv31, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s31 v30 v47 _ _ hinv31 h64 h_v30 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s32, hinv32, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s32 v29 v48 _ _ hinv32 h64 h_v29 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s33, hinv33, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  case_done hinv33 hG with h_v49 in EoCases.__eo_prog_str_update_rev.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18

/-- logos's `__eo_prog_str_update_rev` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstr_2dupdate_2drev.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_str_update_rev.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_str_update_rev
  unfold EoCases.__eo_prog_str_update_rev.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fstr_2dupdate_2drev s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstr_2dupdate_2drev.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fstr_2dupdate_2drev
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_str_update_rev.case_0

theorem eo__24eo_5fprog_5fstr_2dupdate_2drev_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstr_2dupdate_2drev.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fstr_2dupdate_2drev
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstr_2dupdate_2drev s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_str_update_rev x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstr_2dupdate_2drev_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5fcode_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstring_5fcode_5finj s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_code_inj.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_code_inj.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5fcode_5finj more_0_eo__24eo_5fprog_5fstring_5fcode_5finj more_1_eo__24eo_5fprog_5fstring_5fcode_5finj
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a0 _ _ hinv3 h64 h_v2 h_a0 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s5 1#u32 (-1) (by scalar_tac) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v0 v6 _ _ hinv7 h64 h_v0 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_or.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_not.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s11 e_v11 (by rw [he_v11]; exact empty_args) hinv11 h64 as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v11 a0 _ _ hinv12 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with Store.apply_rep s13 v10 v12 _ _ hinv13 h64 h_v10 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_str_2eto_5fcode.construct s14 e_v14 (by rw [he_v14]; exact empty_args) hinv14 h64 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s15 v14 a1 _ _ hinv15 h64 h_v14 h_a1 (by ns_tac) (by ns_tac) as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s16 v13 v15 _ _ hinv16 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s17 v9 v16 _ _ hinv17 h64 h_v9 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s18 v8 v17 _ _ hinv18 h64 h_v8 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_or.construct s19 e_v19 (by rw [he_v19]; exact empty_args) hinv19 h64 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo__3d.construct s20 e_v20 (by rw [he_v20]; exact empty_args) hinv20 h64 as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s21 v20 a0 _ _ hinv21 h64 h_v20 h_a0 (by ns_tac) (by ns_tac) as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s22 v21 a1 _ _ hinv22 h64 h_v21 h_a1 (by ns_tac) (by ns_tac) as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v19 v22 _ _ hinv23 h64 h_v19 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.literal_boolean_spec s24 false hinv24 h64 as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s25 v23 v24 _ _ hinv25 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s26 v18 v25 _ _ hinv26 h64 h_v18 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s27 v7 v26 _ _ hinv27 h64 h_v7 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  case_done hinv28 hG with h_v27 in EoCases.__eo_prog_string_code_inj.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_string_code_inj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5fcode_5finj.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_string_code_inj x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_string_code_inj.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_code_inj
  unfold EoCases.__eo_prog_string_code_inj.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5fcode_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fstring_5fcode_5finj s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_code_inj x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5fcode_5finj.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fstring_5fcode_5finj
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstring_5fcode_5finj_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_string_code_inj.case_0

theorem eo__24eo_5fprog_5fstring_5fcode_5finj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5fcode_5finj.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fstring_5fcode_5finj
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5fcode_5finj s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_string_code_inj x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5fcode_5finj_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5fdecompose_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstring_5fdecompose s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_decompose.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_decompose.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5fdecompose more_10_eo__24eo_5fprog_5fstring_5fdecompose
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_string_decompose.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_string_decompose.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_string_decompose.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_string_decompose.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_string_decompose.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v11, x_v11, h_v11⟩ else hinv2 hG in EoCases.__eo_prog_string_decompose.case_0
  pat_unapply h_v11 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_string_decompose.case_0
  pat_unapply h_v13 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_string_decompose.case_0
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3e_3d.construct s2 e_v18 (by rw [he_v18]; exact empty_args) hinv2 h64 as ⟨v18, s3, hinv3, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17
  pat_same v16 v18 with h_v16 h_v18 using hinv3 else hinv3 hG in EoCases.__eo_prog_string_decompose.case_0
  pat_unapply h_v17 as ⟨v20, v21, x_v20, x_v21, h_v20, h_v21, hn_v20, hn_v21⟩ using hinv3 else hinv3 hG in EoCases.__eo_prog_string_decompose.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v22 (by rw [he_v22]; exact empty_args) hinv3 h64 as ⟨v22, s4, hinv4, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21
  pat_same v20 v22 with h_v20 h_v22 using hinv4 else hinv4 hG in EoCases.__eo_prog_string_decompose.case_0
  pat_same v14 v7 with h_v14 h_v7 using hinv4 else hinv4 hG in EoCases.__eo_prog_string_decompose.case_0
  have h_ite_v149 := (show if_9_eo__24eo_5fprog_5fstring_5fdecompose s4 a0 v21 v7 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_9_eo__24eo_5fprog_5fstring_5fdecompose more_0_eo__24eo_5fprog_5fstring_5fdecompose more_1_eo__24eo_5fprog_5fstring_5fdecompose more_2_eo__24eo_5fprog_5fstring_5fdecompose more_3_eo__24eo_5fprog_5fstring_5fdecompose more_4_eo__24eo_5fprog_5fstring_5fdecompose more_5_eo__24eo_5fprog_5fstring_5fdecompose more_6_eo__24eo_5fprog_5fstring_5fdecompose more_7_eo__24eo_5fprog_5fstring_5fdecompose more_8_eo__24eo_5fprog_5fstring_5fdecompose
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    rcases Store.boolean_value_term h_a0 with ⟨hx_23, hbv_23⟩ | ⟨hx_23, hbv_23⟩ | ⟨hx_23, hbv_23⟩
    · ite_branch hbv_23
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo_and.construct s4 e_v23 (by rw [he_v23]; exact empty_args) hinv4 h64 as ⟨v23, s5, hinv5, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22
      step as ⟨e_v24, he_v24⟩
      store_step with CtorSpec.eo__3d.construct s5 e_v24 (by rw [he_v24]; exact empty_args) hinv5 h64 as ⟨v24, s6, hinv6, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23
      store_step with Store.apply_rep s6 v24 v21 _ _ hinv6 h64 h_v24 h_v21 (by ns_tac) (by ns_tac) as ⟨v25, s7, hinv7, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v26 (by rw [he_v26]; exact empty_args) hinv7 h64 as ⟨v26, s8, hinv8, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo__40purify.construct s8 e_v27 (by rw [he_v27]; exact empty_args) hinv8 h64 as ⟨v27, s9, hinv9, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
      step as ⟨e_v28, he_v28⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s9 e_v28 (by rw [he_v28]; exact empty_args) hinv9 h64 as ⟨v28, s10, hinv10, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
      store_step with Store.apply_rep s10 v28 v21 _ _ hinv10 h64 h_v28 h_v21 (by ns_tac) (by ns_tac) as ⟨v29, s11, hinv11, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v30, s12, hinv12, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
      store_step with Store.apply_rep s12 v29 v30 _ _ hinv12 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s13, hinv13, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
      step as ⟨e_v32, he_v32⟩
      store_step with CtorSpec.eo__2d.construct s13 e_v32 (by rw [he_v32]; exact empty_args) hinv13 h64 as ⟨v32, s14, hinv14, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
      step as ⟨e_v33, he_v33⟩
      store_step with CtorSpec.eo_str_2elen.construct s14 e_v33 (by rw [he_v33]; exact empty_args) hinv14 h64 as ⟨v33, s15, hinv15, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
      store_step with Store.apply_rep s15 v33 v21 _ _ hinv15 h64 h_v33 h_v21 (by ns_tac) (by ns_tac) as ⟨v34, s16, hinv16, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
      store_step with Store.apply_rep s16 v32 v34 _ _ hinv16 h64 h_v32 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s17, hinv17, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
      store_step with Store.apply_rep s17 v35 v7 _ _ hinv17 h64 h_v35 h_v7 (by ns_tac) (by ns_tac) as ⟨v36, s18, hinv18, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
      store_step with Store.apply_rep s18 v31 v36 _ _ hinv18 h64 h_v31 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s19, hinv19, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
      store_step with Store.apply_rep s19 v27 v37 _ _ hinv19 h64 h_v27 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s20, hinv20, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
      store_step with Store.apply_rep s20 v26 v38 _ _ hinv20 h64 h_v26 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s21, hinv21, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
      step as ⟨e_v40, he_v40⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s21 e_v40 (by rw [he_v40]; exact empty_args) hinv21 h64 as ⟨v40, s22, hinv22, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
      step as ⟨e_v41, he_v41⟩
      store_step with CtorSpec.eo__40purify.construct s22 e_v41 (by rw [he_v41]; exact empty_args) hinv22 h64 as ⟨v41, s23, hinv23, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
      step as ⟨e_v42, he_v42⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s23 e_v42 (by rw [he_v42]; exact empty_args) hinv23 h64 as ⟨v42, s24, hinv24, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
      store_step with Store.apply_rep s24 v42 v21 _ _ hinv24 h64 h_v42 h_v21 (by ns_tac) (by ns_tac) as ⟨v43, s25, hinv25, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
      step as ⟨e_v44, he_v44⟩
      store_step with CtorSpec.eo__2d.construct s25 e_v44 (by rw [he_v44]; exact empty_args) hinv25 h64 as ⟨v44, s26, hinv26, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
      step as ⟨e_v45, he_v45⟩
      store_step with CtorSpec.eo_str_2elen.construct s26 e_v45 (by rw [he_v45]; exact empty_args) hinv26 h64 as ⟨v45, s27, hinv27, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
      store_step with Store.apply_rep s27 v45 v21 _ _ hinv27 h64 h_v45 h_v21 (by ns_tac) (by ns_tac) as ⟨v46, s28, hinv28, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
      store_step with Store.apply_rep s28 v44 v46 _ _ hinv28 h64 h_v44 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s29, hinv29, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
      store_step with Store.apply_rep s29 v47 v7 _ _ hinv29 h64 h_v47 h_v7 (by ns_tac) (by ns_tac) as ⟨v48, s30, hinv30, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
      store_step with Store.apply_rep s30 v43 v48 _ _ hinv30 h64 h_v43 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s31, hinv31, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
      store_step with Store.apply_rep s31 v49 v7 _ _ hinv31 h64 h_v49 h_v7 (by ns_tac) (by ns_tac) as ⟨v50, s32, hinv32, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
      store_step with Store.apply_rep s32 v41 v50 _ _ hinv32 h64 h_v41 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s33, hinv33, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
      store_step with Store.apply_rep s33 v40 v51 _ _ hinv33 h64 h_v40 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s34, hinv34, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
      step as ⟨e_v53, he_v53⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s34 e_v53 (by rw [he_v53]; exact empty_args) hinv34 h64 as ⟨v53, s35, hinv35, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
      step as ⟨e_v54, he_v54⟩
      store_step with CtorSpec.eo__40purify.construct s35 e_v54 (by rw [he_v54]; exact empty_args) hinv35 h64 as ⟨v54, s36, hinv36, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
      step as ⟨e_v55, he_v55⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s36 e_v55 (by rw [he_v55]; exact empty_args) hinv36 h64 as ⟨v55, s37, hinv37, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
      store_step with Store.apply_rep s37 v55 v21 _ _ hinv37 h64 h_v55 h_v21 (by ns_tac) (by ns_tac) as ⟨v56, s38, hinv38, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s38 0#u32 (0) (by scalar_tac) hinv38 h64 as ⟨v57, s39, hinv39, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
      store_step with Store.apply_rep s39 v56 v57 _ _ hinv39 h64 h_v56 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s40, hinv40, h_v58⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
      step as ⟨e_v59, he_v59⟩
      store_step with CtorSpec.eo__2d.construct s40 e_v59 (by rw [he_v59]; exact empty_args) hinv40 h64 as ⟨v59, s41, hinv41, h_v59⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58
      step as ⟨e_v60, he_v60⟩
      store_step with CtorSpec.eo_str_2elen.construct s41 e_v60 (by rw [he_v60]; exact empty_args) hinv41 h64 as ⟨v60, s42, hinv42, h_v60⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59
      store_step with Store.apply_rep s42 v60 v21 _ _ hinv42 h64 h_v60 h_v21 (by ns_tac) (by ns_tac) as ⟨v61, s43, hinv43, h_v61⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60
      store_step with Store.apply_rep s43 v59 v61 _ _ hinv43 h64 h_v59 h_v61 (by ns_tac) (by ns_tac) as ⟨v62, s44, hinv44, h_v62⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61
      store_step with Store.apply_rep s44 v62 v7 _ _ hinv44 h64 h_v62 h_v7 (by ns_tac) (by ns_tac) as ⟨v63, s45, hinv45, h_v63⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62
      store_step with Store.apply_rep s45 v58 v63 _ _ hinv45 h64 h_v58 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s46, hinv46, h_v64⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63
      store_step with Store.apply_rep s46 v54 v64 _ _ hinv46 h64 h_v54 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s47, hinv47, h_v65⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64
      store_step with ih.eo__24eo_5ftypeof s47 v65 _ hinv47 h64 (hG.rem hrem) h_v65 as ⟨v66, s48, hinv48, h_v66⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65
      store_step with ih.eo__24eo_5fnil s48 v53 v66 _ _ hinv48 h64 (hG.rem hrem) h_v53 h_v66 as ⟨v67, s49, hinv49, h_v67⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66
      store_step with Store.apply_mk_rep s49 v52 v67 _ _ hinv49 h64 h_v52 h_v67 as ⟨v68, s50, hinv50, h_v68⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67
      store_step with Store.apply_mk_rep s50 v39 v68 _ _ hinv50 h64 h_v39 h_v68 as ⟨v69, s51, hinv51, h_v69⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68
      store_step with Store.apply_mk_rep s51 v25 v69 _ _ hinv51 h64 h_v25 h_v69 as ⟨v70, s52, hinv52, h_v70⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69
      store_step with Store.apply_mk_rep s52 v23 v70 _ _ hinv52 h64 h_v23 h_v70 as ⟨v71, s53, hinv53, h_v71⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70
      step as ⟨e_v72, he_v72⟩
      store_step with CtorSpec.eo_and.construct s53 e_v72 (by rw [he_v72]; exact empty_args) hinv53 h64 as ⟨v72, s54, hinv54, h_v72⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71
      step as ⟨e_v73, he_v73⟩
      store_step with CtorSpec.eo__3d.construct s54 e_v73 (by rw [he_v73]; exact empty_args) hinv54 h64 as ⟨v73, s55, hinv55, h_v73⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72
      step as ⟨e_v74, he_v74⟩
      store_step with CtorSpec.eo_str_2elen.construct s55 e_v74 (by rw [he_v74]; exact empty_args) hinv55 h64 as ⟨v74, s56, hinv56, h_v74⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73
      step as ⟨e_v75, he_v75⟩
      store_step with CtorSpec.eo__40purify.construct s56 e_v75 (by rw [he_v75]; exact empty_args) hinv56 h64 as ⟨v75, s57, hinv57, h_v75⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74
      step as ⟨e_v76, he_v76⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s57 e_v76 (by rw [he_v76]; exact empty_args) hinv57 h64 as ⟨v76, s58, hinv58, h_v76⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75
      store_step with Store.apply_rep s58 v76 v21 _ _ hinv58 h64 h_v76 h_v21 (by ns_tac) (by ns_tac) as ⟨v77, s59, hinv59, h_v77⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76
      step as ⟨e_v78, he_v78⟩
      store_step with CtorSpec.eo__2d.construct s59 e_v78 (by rw [he_v78]; exact empty_args) hinv59 h64 as ⟨v78, s60, hinv60, h_v78⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77
      step as ⟨e_v79, he_v79⟩
      store_step with CtorSpec.eo_str_2elen.construct s60 e_v79 (by rw [he_v79]; exact empty_args) hinv60 h64 as ⟨v79, s61, hinv61, h_v79⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78
      store_step with Store.apply_rep s61 v79 v21 _ _ hinv61 h64 h_v79 h_v21 (by ns_tac) (by ns_tac) as ⟨v80, s62, hinv62, h_v80⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79
      store_step with Store.apply_rep s62 v78 v80 _ _ hinv62 h64 h_v78 h_v80 (by ns_tac) (by ns_tac) as ⟨v81, s63, hinv63, h_v81⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80
      store_step with Store.apply_rep s63 v81 v7 _ _ hinv63 h64 h_v81 h_v7 (by ns_tac) (by ns_tac) as ⟨v82, s64, hinv64, h_v82⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81
      store_step with Store.apply_rep s64 v77 v82 _ _ hinv64 h64 h_v77 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s65, hinv65, h_v83⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82
      store_step with Store.apply_rep s65 v83 v7 _ _ hinv65 h64 h_v83 h_v7 (by ns_tac) (by ns_tac) as ⟨v84, s66, hinv66, h_v84⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83
      store_step with Store.apply_rep s66 v75 v84 _ _ hinv66 h64 h_v75 h_v84 (by ns_tac) (by ns_tac) as ⟨v85, s67, hinv67, h_v85⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84
      store_step with Store.apply_rep s67 v74 v85 _ _ hinv67 h64 h_v74 h_v85 (by ns_tac) (by ns_tac) as ⟨v86, s68, hinv68, h_v86⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85
      store_step with Store.apply_rep s68 v73 v86 _ _ hinv68 h64 h_v73 h_v86 (by ns_tac) (by ns_tac) as ⟨v87, s69, hinv69, h_v87⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86
      store_step with Store.apply_rep s69 v87 v7 _ _ hinv69 h64 h_v87 h_v7 (by ns_tac) (by ns_tac) as ⟨v88, s70, hinv70, h_v88⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87
      store_step with Store.apply_rep s70 v72 v88 _ _ hinv70 h64 h_v72 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s71, hinv71, h_v89⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88
      store_step with Store.literal_boolean_spec s71 true hinv71 h64 as ⟨v90, s72, hinv72, h_v90⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89
      store_step with Store.apply_rep s72 v89 v90 _ _ hinv72 h64 h_v89 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s73, hinv73, h_v91⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90
      store_step with Store.apply_mk_rep s73 v71 v91 _ _ hinv73 h64 h_v71 h_v91 as ⟨v92, s74, hinv74, h_v92⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57 h_v58 h_v59 h_v60 h_v61 h_v62 h_v63 h_v64 h_v65 h_v66 h_v67 h_v68 h_v69 h_v70 h_v71 h_v72 h_v73 h_v74 h_v75 h_v76 h_v77 h_v78 h_v79 h_v80 h_v81 h_v82 h_v83 h_v84 h_v85 h_v86 h_v87 h_v88 h_v89 h_v90 h_v91
      ite_done hinv74 hG with (eo_ite_true_rep _ hx_23 h_v92)
    · ite_branch hbv_23
      step as ⟨e_v93, he_v93⟩
      store_step with CtorSpec.eo_and.construct s4 e_v93 (by rw [he_v93]; exact empty_args) hinv4 h64 as ⟨v93, s5, hinv5, h_v93⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22
      step as ⟨e_v94, he_v94⟩
      store_step with CtorSpec.eo__3d.construct s5 e_v94 (by rw [he_v94]; exact empty_args) hinv5 h64 as ⟨v94, s6, hinv6, h_v94⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93
      store_step with Store.apply_rep s6 v94 v21 _ _ hinv6 h64 h_v94 h_v21 (by ns_tac) (by ns_tac) as ⟨v95, s7, hinv7, h_v95⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94
      step as ⟨e_v96, he_v96⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s7 e_v96 (by rw [he_v96]; exact empty_args) hinv7 h64 as ⟨v96, s8, hinv8, h_v96⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95
      step as ⟨e_v97, he_v97⟩
      store_step with CtorSpec.eo__40purify.construct s8 e_v97 (by rw [he_v97]; exact empty_args) hinv8 h64 as ⟨v97, s9, hinv9, h_v97⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96
      step as ⟨e_v98, he_v98⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s9 e_v98 (by rw [he_v98]; exact empty_args) hinv9 h64 as ⟨v98, s10, hinv10, h_v98⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97
      store_step with Store.apply_rep s10 v98 v21 _ _ hinv10 h64 h_v98 h_v21 (by ns_tac) (by ns_tac) as ⟨v99, s11, hinv11, h_v99⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v100, s12, hinv12, h_v100⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99
      store_step with Store.apply_rep s12 v99 v100 _ _ hinv12 h64 h_v99 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s13, hinv13, h_v101⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100
      store_step with Store.apply_rep s13 v101 v7 _ _ hinv13 h64 h_v101 h_v7 (by ns_tac) (by ns_tac) as ⟨v102, s14, hinv14, h_v102⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101
      store_step with Store.apply_rep s14 v97 v102 _ _ hinv14 h64 h_v97 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s15, hinv15, h_v103⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102
      store_step with Store.apply_rep s15 v96 v103 _ _ hinv15 h64 h_v96 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s16, hinv16, h_v104⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103
      step as ⟨e_v105, he_v105⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s16 e_v105 (by rw [he_v105]; exact empty_args) hinv16 h64 as ⟨v105, s17, hinv17, h_v105⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104
      step as ⟨e_v106, he_v106⟩
      store_step with CtorSpec.eo__40purify.construct s17 e_v106 (by rw [he_v106]; exact empty_args) hinv17 h64 as ⟨v106, s18, hinv18, h_v106⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105
      step as ⟨e_v107, he_v107⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s18 e_v107 (by rw [he_v107]; exact empty_args) hinv18 h64 as ⟨v107, s19, hinv19, h_v107⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106
      store_step with Store.apply_rep s19 v107 v21 _ _ hinv19 h64 h_v107 h_v21 (by ns_tac) (by ns_tac) as ⟨v108, s20, hinv20, h_v108⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107
      store_step with Store.apply_rep s20 v108 v7 _ _ hinv20 h64 h_v108 h_v7 (by ns_tac) (by ns_tac) as ⟨v109, s21, hinv21, h_v109⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108
      step as ⟨e_v110, he_v110⟩
      store_step with CtorSpec.eo__2d.construct s21 e_v110 (by rw [he_v110]; exact empty_args) hinv21 h64 as ⟨v110, s22, hinv22, h_v110⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109
      step as ⟨e_v111, he_v111⟩
      store_step with CtorSpec.eo_str_2elen.construct s22 e_v111 (by rw [he_v111]; exact empty_args) hinv22 h64 as ⟨v111, s23, hinv23, h_v111⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110
      store_step with Store.apply_rep s23 v111 v21 _ _ hinv23 h64 h_v111 h_v21 (by ns_tac) (by ns_tac) as ⟨v112, s24, hinv24, h_v112⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111
      store_step with Store.apply_rep s24 v110 v112 _ _ hinv24 h64 h_v110 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s25, hinv25, h_v113⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112
      store_step with Store.apply_rep s25 v113 v7 _ _ hinv25 h64 h_v113 h_v7 (by ns_tac) (by ns_tac) as ⟨v114, s26, hinv26, h_v114⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113
      store_step with Store.apply_rep s26 v109 v114 _ _ hinv26 h64 h_v109 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s27, hinv27, h_v115⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114
      store_step with Store.apply_rep s27 v106 v115 _ _ hinv27 h64 h_v106 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s28, hinv28, h_v116⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115
      store_step with Store.apply_rep s28 v105 v116 _ _ hinv28 h64 h_v105 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s29, hinv29, h_v117⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116
      step as ⟨e_v118, he_v118⟩
      store_step with CtorSpec.eo_str_2e_2b_2b.construct s29 e_v118 (by rw [he_v118]; exact empty_args) hinv29 h64 as ⟨v118, s30, hinv30, h_v118⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117
      step as ⟨e_v119, he_v119⟩
      store_step with CtorSpec.eo__40purify.construct s30 e_v119 (by rw [he_v119]; exact empty_args) hinv30 h64 as ⟨v119, s31, hinv31, h_v119⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118
      step as ⟨e_v120, he_v120⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s31 e_v120 (by rw [he_v120]; exact empty_args) hinv31 h64 as ⟨v120, s32, hinv32, h_v120⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119
      store_step with Store.apply_rep s32 v120 v21 _ _ hinv32 h64 h_v120 h_v21 (by ns_tac) (by ns_tac) as ⟨v121, s33, hinv33, h_v121⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s33 0#u32 (0) (by scalar_tac) hinv33 h64 as ⟨v122, s34, hinv34, h_v122⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121
      store_step with Store.apply_rep s34 v121 v122 _ _ hinv34 h64 h_v121 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s35, hinv35, h_v123⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122
      store_step with Store.apply_rep s35 v123 v7 _ _ hinv35 h64 h_v123 h_v7 (by ns_tac) (by ns_tac) as ⟨v124, s36, hinv36, h_v124⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123
      store_step with Store.apply_rep s36 v119 v124 _ _ hinv36 h64 h_v119 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s37, hinv37, h_v125⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124
      store_step with ih.eo__24eo_5ftypeof s37 v125 _ hinv37 h64 (hG.rem hrem) h_v125 as ⟨v126, s38, hinv38, h_v126⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125
      store_step with ih.eo__24eo_5fnil s38 v118 v126 _ _ hinv38 h64 (hG.rem hrem) h_v118 h_v126 as ⟨v127, s39, hinv39, h_v127⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126
      store_step with Store.apply_mk_rep s39 v117 v127 _ _ hinv39 h64 h_v117 h_v127 as ⟨v128, s40, hinv40, h_v128⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127
      store_step with Store.apply_mk_rep s40 v104 v128 _ _ hinv40 h64 h_v104 h_v128 as ⟨v129, s41, hinv41, h_v129⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128
      store_step with Store.apply_mk_rep s41 v95 v129 _ _ hinv41 h64 h_v95 h_v129 as ⟨v130, s42, hinv42, h_v130⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129
      store_step with Store.apply_mk_rep s42 v93 v130 _ _ hinv42 h64 h_v93 h_v130 as ⟨v131, s43, hinv43, h_v131⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130
      step as ⟨e_v132, he_v132⟩
      store_step with CtorSpec.eo_and.construct s43 e_v132 (by rw [he_v132]; exact empty_args) hinv43 h64 as ⟨v132, s44, hinv44, h_v132⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131
      step as ⟨e_v133, he_v133⟩
      store_step with CtorSpec.eo__3d.construct s44 e_v133 (by rw [he_v133]; exact empty_args) hinv44 h64 as ⟨v133, s45, hinv45, h_v133⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132
      step as ⟨e_v134, he_v134⟩
      store_step with CtorSpec.eo_str_2elen.construct s45 e_v134 (by rw [he_v134]; exact empty_args) hinv45 h64 as ⟨v134, s46, hinv46, h_v134⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133
      step as ⟨e_v135, he_v135⟩
      store_step with CtorSpec.eo__40purify.construct s46 e_v135 (by rw [he_v135]; exact empty_args) hinv46 h64 as ⟨v135, s47, hinv47, h_v135⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134
      step as ⟨e_v136, he_v136⟩
      store_step with CtorSpec.eo_str_2esubstr.construct s47 e_v136 (by rw [he_v136]; exact empty_args) hinv47 h64 as ⟨v136, s48, hinv48, h_v136⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135
      store_step with Store.apply_rep s48 v136 v21 _ _ hinv48 h64 h_v136 h_v21 (by ns_tac) (by ns_tac) as ⟨v137, s49, hinv49, h_v137⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s49 0#u32 (0) (by scalar_tac) hinv49 h64 as ⟨v138, s50, hinv50, h_v138⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137
      store_step with Store.apply_rep s50 v137 v138 _ _ hinv50 h64 h_v137 h_v138 (by ns_tac) (by ns_tac) as ⟨v139, s51, hinv51, h_v139⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138
      store_step with Store.apply_rep s51 v139 v7 _ _ hinv51 h64 h_v139 h_v7 (by ns_tac) (by ns_tac) as ⟨v140, s52, hinv52, h_v140⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139
      store_step with Store.apply_rep s52 v135 v140 _ _ hinv52 h64 h_v135 h_v140 (by ns_tac) (by ns_tac) as ⟨v141, s53, hinv53, h_v141⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140
      store_step with Store.apply_rep s53 v134 v141 _ _ hinv53 h64 h_v134 h_v141 (by ns_tac) (by ns_tac) as ⟨v142, s54, hinv54, h_v142⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141
      store_step with Store.apply_rep s54 v133 v142 _ _ hinv54 h64 h_v133 h_v142 (by ns_tac) (by ns_tac) as ⟨v143, s55, hinv55, h_v143⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142
      store_step with Store.apply_rep s55 v143 v7 _ _ hinv55 h64 h_v143 h_v7 (by ns_tac) (by ns_tac) as ⟨v144, s56, hinv56, h_v144⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142 h_v143
      store_step with Store.apply_rep s56 v132 v144 _ _ hinv56 h64 h_v132 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s57, hinv57, h_v145⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142 h_v143 h_v144
      store_step with Store.literal_boolean_spec s57 true hinv57 h64 as ⟨v146, s58, hinv58, h_v146⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142 h_v143 h_v144 h_v145
      store_step with Store.apply_rep s58 v145 v146 _ _ hinv58 h64 h_v145 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s59, hinv59, h_v147⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146
      store_step with Store.apply_mk_rep s59 v131 v147 _ _ hinv59 h64 h_v131 h_v147 as ⟨v148, s60, hinv60, h_v148⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22 h_v93 h_v94 h_v95 h_v96 h_v97 h_v98 h_v99 h_v100 h_v101 h_v102 h_v103 h_v104 h_v105 h_v106 h_v107 h_v108 h_v109 h_v110 h_v111 h_v112 h_v113 h_v114 h_v115 h_v116 h_v117 h_v118 h_v119 h_v120 h_v121 h_v122 h_v123 h_v124 h_v125 h_v126 h_v127 h_v128 h_v129 h_v130 h_v131 h_v132 h_v133 h_v134 h_v135 h_v136 h_v137 h_v138 h_v139 h_v140 h_v141 h_v142 h_v143 h_v144 h_v145 h_v146 h_v147
      ite_done hinv60 hG with (eo_ite_false_rep _ hx_23 h_v148)
    · ite_branch hbv_23
      ite_stuck hinv4 hG with hx_23)
  store_step with h_ite_v149 as ⟨v149, s5, hinv5, h_v149⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v9 h_v11 h_v13 h_v14 h_v16 h_v17 h_v18 h_v20 h_v21 h_v22
  case_done hinv5 hG with h_v149 in EoCases.__eo_prog_string_decompose.case_0 using hn_a0 hn_v3 hn_v4 hn_v6 hn_v7 hn_v13 hn_v14 hn_v16 hn_v17 hn_v20 hn_v21

/-- logos's `__eo_prog_string_decompose` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5fdecompose.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_string_decompose x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_string_decompose.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_decompose
  unfold EoCases.__eo_prog_string_decompose.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5fdecompose_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fstring_5fdecompose s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_decompose x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5fdecompose.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fstring_5fdecompose
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstring_5fdecompose_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_string_decompose.case_0

theorem eo__24eo_5fprog_5fstring_5fdecompose_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5fdecompose.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fstring_5fdecompose
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5fdecompose s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_string_decompose x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5fdecompose_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5feager_5freduction_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstring_5feager_5freduction s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_eager_reduction.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_eager_reduction.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5feager_5freduction
  have hG := Store.Grows.refl s
  store_step with ih.eo__24mk_5fstr_5feager_5freduction s a0 _ hinv h64 hrem h_a0 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  case_done hinv1 hG with h_v0 in EoCases.__eo_prog_string_eager_reduction.case_0 using hn_a0

/-- logos's `__eo_prog_string_eager_reduction` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5feager_5freduction.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_eager_reduction x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_string_eager_reduction.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_eager_reduction
  unfold EoCases.__eo_prog_string_eager_reduction.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5feager_5freduction_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5feager_5freduction s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_eager_reduction x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5feager_5freduction.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5feager_5freduction
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstring_5feager_5freduction_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_string_eager_reduction.case_0

theorem eo__24eo_5fprog_5fstring_5feager_5freduction_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5feager_5freduction.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5feager_5freduction
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5feager_5freduction s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_eager_reduction x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5feager_5freduction_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5fext_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fstring_5fext s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_ext.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_ext.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5fext more_0_eo__24eo_5fprog_5fstring_5fext more_1_eo__24eo_5fprog_5fstring_5fext more_2_eo__24eo_5fprog_5fstring_5fext more_3_eo__24eo_5fprog_5fstring_5fext
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_string_ext.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_string_ext.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_string_ext.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_ext.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_ext.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_string_ext.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_or.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_not.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_str_2elen.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v16 v11 _ _ hinv6 h64 h_v16 h_v11 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v15 v17 _ _ hinv7 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_str_2elen.construct s8 e_v19 (by rw [he_v19]; exact empty_args) hinv8 h64 as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_rep s9 v19 v8 _ _ hinv9 h64 h_v19 h_v8 (by ns_tac) (by ns_tac) as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s10 v18 v20 _ _ hinv10 h64 h_v18 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v14 v21 _ _ hinv11 h64 h_v14 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s12 v13 v22 _ _ hinv12 h64 h_v13 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_or.construct s13 e_v24 (by rw [he_v24]; exact empty_args) hinv13 h64 as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_and.construct s14 e_v25 (by rw [he_v25]; exact empty_args) hinv14 h64 as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40strings_5fdeq_5fdiff.construct s15 e_v26 (by rw [he_v26]; exact empty_args) hinv15 h64 as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s16 v26 v11 _ _ hinv16 h64 h_v26 h_v11 (by ns_tac) (by ns_tac) as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s17 v27 v8 _ _ hinv17 h64 h_v27 h_v8 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with ih.eo__24eo_5ftypeof s18 v11 _ hinv18 h64 (hG.rem hrem) h_v11 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with ih.eo__24str_5fmk_5fext_5fdeq s19 v11 v8 v28 v29 _ _ _ _ hinv19 h64 (hG.rem hrem) h_v11 h_v8 h_v28 h_v29 as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_mk_rep s20 v25 v30 _ _ hinv20 h64 h_v25 h_v30 as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_and.construct s21 e_v32 (by rw [he_v32]; exact empty_args) hinv21 h64 as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3c_3d.construct s22 e_v33 (by rw [he_v33]; exact empty_args) hinv22 h64 as ⟨v33, s23, hinv23, h_v33⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s23 0#u32 (0) (by scalar_tac) hinv23 h64 as ⟨v34, s24, hinv24, h_v34⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s24 v33 v34 _ _ hinv24 h64 h_v33 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s25, hinv25, h_v35⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__40strings_5fdeq_5fdiff.construct s25 e_v36 (by rw [he_v36]; exact empty_args) hinv25 h64 as ⟨v36, s26, hinv26, h_v36⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.apply_rep s26 v36 v11 _ _ hinv26 h64 h_v36 h_v11 (by ns_tac) (by ns_tac) as ⟨v37, s27, hinv27, h_v37⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s27 v37 v8 _ _ hinv27 h64 h_v37 h_v8 (by ns_tac) (by ns_tac) as ⟨v38, s28, hinv28, h_v38⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s28 v35 v38 _ _ hinv28 h64 h_v35 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s29, hinv29, h_v39⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s29 v32 v39 _ _ hinv29 h64 h_v32 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s30, hinv30, h_v40⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_and.construct s30 e_v41 (by rw [he_v41]; exact empty_args) hinv30 h64 as ⟨v41, s31, hinv31, h_v41⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__3c.construct s31 e_v42 (by rw [he_v42]; exact empty_args) hinv31 h64 as ⟨v42, s32, hinv32, h_v42⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo__40strings_5fdeq_5fdiff.construct s32 e_v43 (by rw [he_v43]; exact empty_args) hinv32 h64 as ⟨v43, s33, hinv33, h_v43⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s33 v43 v11 _ _ hinv33 h64 h_v43 h_v11 (by ns_tac) (by ns_tac) as ⟨v44, s34, hinv34, h_v44⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s34 v44 v8 _ _ hinv34 h64 h_v44 h_v8 (by ns_tac) (by ns_tac) as ⟨v45, s35, hinv35, h_v45⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s35 v42 v45 _ _ hinv35 h64 h_v42 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s36, hinv36, h_v46⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_str_2elen.construct s36 e_v47 (by rw [he_v47]; exact empty_args) hinv36 h64 as ⟨v47, s37, hinv37, h_v47⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s37 v47 v11 _ _ hinv37 h64 h_v47 h_v11 (by ns_tac) (by ns_tac) as ⟨v48, s38, hinv38, h_v48⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  store_step with Store.apply_rep s38 v46 v48 _ _ hinv38 h64 h_v46 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s39, hinv39, h_v49⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s39 v41 v49 _ _ hinv39 h64 h_v41 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s40, hinv40, h_v50⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.literal_boolean_spec s40 true hinv40 h64 as ⟨v51, s41, hinv41, h_v51⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_rep s41 v50 v51 _ _ hinv41 h64 h_v50 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s42, hinv42, h_v52⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s42 v40 v52 _ _ hinv42 h64 h_v40 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s43, hinv43, h_v53⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  store_step with Store.apply_mk_rep s43 v31 v53 _ _ hinv43 h64 h_v31 h_v53 as ⟨v54, s44, hinv44, h_v54⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_mk_rep s44 v24 v54 _ _ hinv44 h64 h_v24 h_v54 as ⟨v55, s45, hinv45, h_v55⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.literal_boolean_spec s45 false hinv45 h64 as ⟨v56, s46, hinv46, h_v56⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_mk_rep s46 v55 v56 _ _ hinv46 h64 h_v55 h_v56 as ⟨v57, s47, hinv47, h_v57⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  store_step with Store.apply_mk_rep s47 v23 v57 _ _ hinv47 h64 h_v23 h_v57 as ⟨v58, s48, hinv48, h_v58⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56 h_v57
  case_done hinv48 hG with h_v58 in EoCases.__eo_prog_string_ext.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_string_ext` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5fext.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_ext x_a0 =
      (firstSome [EoCases.__eo_prog_string_ext.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_ext
  unfold EoCases.__eo_prog_string_ext.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5fext_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5fext s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_ext x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5fext.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5fext
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fstring_5fext_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_string_ext.case_0

theorem eo__24eo_5fprog_5fstring_5fext_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5fext.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5fext
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5fext s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_ext x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5fext_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_length_non_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_length_non_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_string_length_non_empty.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_string_length_non_empty.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_not.construct s e_v5 (by rw [he_v5]; exact empty_args) hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv1 else hinv1 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  pat_unapply h_v4 as ⟨v7, v8, x_v7, x_v8, h_v7, h_v8, hn_v7, hn_v8⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_string_length_non_empty.case_0
  store_step with ih.eo__24str_5fis_5fempty s2 v8 _ hinv2 h64 (hG.rem hrem) h_v8 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  have h_req_v23 := (show requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s4 v13 v14 v11 ⦃ r s' => s'.Inv ∧ s4.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s4
    req_same v13 v14 with h_v13 h_v14 using hinv4 hG
    req_stuck h_v13 as hq_v13 using hinv4 hG
    step as ⟨e_v15, he_v15⟩
    store_step with CtorSpec.eo_not.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__3d.construct s5 e_v16 (by rw [he_v16]; exact empty_args) hinv5 h64 as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
    step as ⟨e_v17, he_v17⟩
    store_step with CtorSpec.eo_str_2elen.construct s6 e_v17 (by rw [he_v17]; exact empty_args) hinv6 h64 as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
    store_step with Store.apply_rep s7 v17 v11 _ _ hinv7 h64 h_v17 h_v11 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
    store_step with Store.apply_rep s8 v16 v18 _ _ hinv8 h64 h_v16 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
    store_step with Store.apply_rep s10 v19 v20 _ _ hinv10 h64 h_v19 h_v20 (by ns_tac) (by ns_tac) as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
    store_step with Store.apply_rep s11 v15 v21 _ _ hinv11 h64 h_v15 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
    req_done hinv12 hG with h_v22 using hq_v13)
  store_step with h_req_v23 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v5 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  case_done hinv13 hG with h_v23 in EoCases.__eo_prog_string_length_non_empty.case_0 using hn_v3 hn_v4 hn_v7 hn_v8 hn_v10 hn_v11

/-- logos's `__eo_prog_string_length_non_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_length_non_empty x_a0 =
      (firstSome [EoCases.__eo_prog_string_length_non_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_length_non_empty
  unfold EoCases.__eo_prog_string_length_non_empty.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_length_non_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_string_length_non_empty.case_0

theorem eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_length_non_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5flength_5fnon_5fempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5flength_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fstring_5flength_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_length_pos.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_length_pos.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5flength_5fpos more_0_eo__24eo_5fprog_5fstring_5flength_5fpos more_1_eo__24eo_5fprog_5fstring_5flength_5fpos
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_and.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_str_2elen.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a0 _ _ hinv4 h64 h_v3 h_a0 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v2 v4 _ _ hinv5 h64 h_v2 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 0#u32 (0) (by scalar_tac) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v5 v6 _ _ hinv7 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v1 v7 _ _ hinv8 h64 h_v1 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_and.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3d.construct s10 e_v10 (by rw [he_v10]; exact empty_args) hinv10 h64 as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v10 a0 _ _ hinv11 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s12 a0 _ hinv12 h64 (hG.rem hrem) h_a0 as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24seq_5fempty s13 v12 _ hinv13 h64 (hG.rem hrem) h_v12 as ⟨v13, s14, hinv14, h_v13⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_mk_rep s14 v11 v13 _ _ hinv14 h64 h_v11 h_v13 as ⟨v14, s15, hinv15, h_v14⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_mk_rep s15 v9 v14 _ _ hinv15 h64 h_v9 h_v14 as ⟨v15, s16, hinv16, h_v15⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.literal_boolean_spec s16 true hinv16 h64 as ⟨v16, s17, hinv17, h_v16⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_mk_rep s17 v15 v16 _ _ hinv17 h64 h_v15 h_v16 as ⟨v17, s18, hinv18, h_v17⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_mk_rep s18 v8 v17 _ _ hinv18 h64 h_v8 h_v17 as ⟨v18, s19, hinv19, h_v18⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_mk_rep s19 v0 v18 _ _ hinv19 h64 h_v0 h_v18 as ⟨v19, s20, hinv20, h_v19⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_or.construct s20 e_v20 (by rw [he_v20]; exact empty_args) hinv20 h64 as ⟨v20, s21, hinv21, h_v20⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3e.construct s21 e_v21 (by rw [he_v21]; exact empty_args) hinv21 h64 as ⟨v21, s22, hinv22, h_v21⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_str_2elen.construct s22 e_v22 (by rw [he_v22]; exact empty_args) hinv22 h64 as ⟨v22, s23, hinv23, h_v22⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s23 v22 a0 _ _ hinv23 h64 h_v22 h_a0 (by ns_tac) (by ns_tac) as ⟨v23, s24, hinv24, h_v23⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s24 v21 v23 _ _ hinv24 h64 h_v21 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s25, hinv25, h_v24⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s25 0#u32 (0) (by scalar_tac) hinv25 h64 as ⟨v25, s26, hinv26, h_v25⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s26 v24 v25 _ _ hinv26 h64 h_v24 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s27, hinv27, h_v26⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s27 v20 v26 _ _ hinv27 h64 h_v20 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s28, hinv28, h_v27⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.literal_boolean_spec s28 false hinv28 h64 as ⟨v28, s29, hinv29, h_v28⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s29 v27 v28 _ _ hinv29 h64 h_v27 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s30, hinv30, h_v29⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_mk_rep s30 v19 v29 _ _ hinv30 h64 h_v19 h_v29 as ⟨v30, s31, hinv31, h_v30⟩ growing hG carrying h_a0 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  case_done hinv31 hG with h_v30 in EoCases.__eo_prog_string_length_pos.case_0 using hn_a0

/-- logos's `__eo_prog_string_length_pos` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5flength_5fpos.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_length_pos x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_string_length_pos.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_length_pos
  unfold EoCases.__eo_prog_string_length_pos.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5flength_5fpos_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5flength_5fpos s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_length_pos x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5flength_5fpos.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5flength_5fpos
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fstring_5flength_5fpos_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_string_length_pos.case_0

theorem eo__24eo_5fprog_5fstring_5flength_5fpos_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5flength_5fpos.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5flength_5fpos
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5flength_5fpos s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_length_pos x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5flength_5fpos_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_string_seq_unit_inj.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_string_seq_unit_inj.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj more_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  pat_unapply h_v4 as ⟨v14, v15, x_v14, x_v15, h_v14, h_v15, hn_v14, hn_v15⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_seq_2eunit.construct s2 e_v16 (by rw [he_v16]; exact empty_args) hinv2 h64 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15
  pat_same v14 v16 with h_v14 h_v16 using hinv3 else hinv3 hG in EoCases.__eo_prog_string_seq_unit_inj.case_0
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v17 (by rw [he_v17]; exact empty_args) hinv3 h64 as ⟨v17, s4, hinv4, h_v17⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s4 v17 v11 _ _ hinv4 h64 h_v17 h_v11 (by ns_tac) (by ns_tac) as ⟨v18, s5, hinv5, h_v18⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s5 v18 v15 _ _ hinv5 h64 h_v18 h_v15 (by ns_tac) (by ns_tac) as ⟨v19, s6, hinv6, h_v19⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv6 hG with h_v19 in EoCases.__eo_prog_string_seq_unit_inj.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v14 hn_v15

/-- logos's `__eo_prog_string_seq_unit_inj` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_string_seq_unit_inj x_a0 =
      (firstSome [EoCases.__eo_prog_string_seq_unit_inj.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_string_seq_unit_inj
  unfold EoCases.__eo_prog_string_seq_unit_inj.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_string_seq_unit_inj x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_string_seq_unit_inj.case_0

theorem eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fstring_5fseq_5funit_5finj.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fstring_5fseq_5funit_5finj
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_string_seq_unit_inj x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_symm.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_symm.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fsymm
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_symm.case_0
  store_step with ih.eo__24mk_5fsymm s v1 _ hinv h64 hrem h_v1 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  case_done hinv1 hG with h_v2 in EoCases.__eo_prog_symm.case_0 using

/-- logos's `__eo_prog_symm` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fsymm.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_symm x_a0 =
      (firstSome [EoCases.__eo_prog_symm.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_symm
  unfold EoCases.__eo_prog_symm.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fsymm s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_symm x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fsymm.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fsymm
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5fsymm_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_symm.case_0

theorem eo__24eo_5fprog_5fsymm_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fsymm.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fsymm
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fsymm s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_symm x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fsymm_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_trans.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_trans.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrans
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_trans.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_and.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_trans.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_trans.case_0
  store_step with ih.eo__24mk_5ftrans s2 v14 v11 v4 _ _ _ hinv2 h64 (hG.rem hrem) h_v14 h_v11 h_v4 as ⟨v16, s3, hinv3, h_v16⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15
  case_done hinv3 hG with h_v16 in EoCases.__eo_prog_trans.case_0 using hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14

/-- logos's `__eo_prog_trans` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrans.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_trans x_a0 =
      (firstSome [EoCases.__eo_prog_trans.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_trans
  unfold EoCases.__eo_prog_trans.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ftrans s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trans x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrans.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrans
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrans_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_trans.case_0

theorem eo__24eo_5fprog_5ftrans_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrans.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ftrans
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrans s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_trans x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrans_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrue_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fprog_5ftrue_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_true_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_true_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrue_5felim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_true_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_true_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_true_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_true_elim.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v9, s2, hinv2, h_v9⟩ growing hG carrying h_a0 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8
  pat_same v4 v9 with h_v4 h_v9 using hinv2 else hinv2 hG in EoCases.__eo_prog_true_elim.case_0
  case_done hinv2 hG with h_v7 in EoCases.__eo_prog_true_elim.case_0 using hn_v3 hn_v4 hn_v6 hn_v7

/-- logos's `__eo_prog_true_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrue_5felim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_true_elim x_a0 =
      (firstSome [EoCases.__eo_prog_true_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_true_elim
  unfold EoCases.__eo_prog_true_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrue_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5ftrue_5felim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_true_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrue_5felim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrue_5felim
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrue_5felim_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_true_elim.case_0

theorem eo__24eo_5fprog_5ftrue_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrue_5felim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5ftrue_5felim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrue_5felim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_true_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrue_5felim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrue_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : ProofOK x_a0) :
    case_0_eo__24eo_5fprog_5ftrue_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_true_intro.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_true_intro.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrue_5fintro
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_true_intro.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s e_v2 (by rw [he_v2]; exact empty_args) hinv h64 as ⟨v2, s1, hinv1, h_v2⟩ growing hG carrying h_a0 h_v1
  have hn_v1 := hg_a0 _ rfl
  store_step with Store.apply_rep s1 v2 v1 _ _ hinv1 h64 h_v2 h_v1 (by ns_tac) (by ns_tac) as ⟨v3, s2, hinv2, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s3 v3 v4 _ _ hinv3 h64 h_v3 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s4, hinv4, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv4 hG with h_v5 in EoCases.__eo_prog_true_intro.case_0 using hn_v1

/-- logos's `__eo_prog_true_intro` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrue_5fintro.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_true_intro x_a0 =
      (firstSome [EoCases.__eo_prog_true_intro.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_true_intro
  unfold EoCases.__eo_prog_true_intro.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrue_5fintro_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hg_a0 : ProofOK x_a0) :
    body_eo__24eo_5fprog_5ftrue_5fintro s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_true_intro x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrue_5fintro.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5ftrue_5fintro
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fprog_5ftrue_5fintro_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_prog_true_intro.case_0

theorem eo__24eo_5fprog_5ftrue_5fintro_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrue_5fintro.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0 hg_a0
  unfold eo__24eo_5fprog_5ftrue_5fintro
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrue_5fintro s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_true_intro x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrue_5fintro_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5ftrust_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5ftrust s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_trust.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_trust.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5ftrust
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_trust.case_0
  case_done hinv hG with h_a0 in EoCases.__eo_prog_trust.case_0 using hn_a0

/-- logos's `__eo_prog_trust` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5ftrust.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_trust x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_trust.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_trust
  unfold EoCases.__eo_prog_trust.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5ftrust_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5ftrust s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_trust x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5ftrust.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5ftrust
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5ftrust_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_trust.case_0

theorem eo__24eo_5fprog_5ftrust_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5ftrust.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5ftrust
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5ftrust s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_trust x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5ftrust_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ubv_to_int_elim.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ubv_to_int_elim.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim more_2_eo__24eo_5fprog_5fubv_2dto_2dint_2delim
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_ubv_to_int_elim.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__eo_prog_ubv_to_int_elim.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__3d.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__eo_prog_ubv_to_int_elim.case_0
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_ubv_to_int_elim.case_0
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s1 e_v10 (by rw [he_v10]; exact empty_args) hinv1 h64 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9
  pat_same v8 v10 with h_v8 h_v10 using hinv2 else hinv2 hG in EoCases.__eo_prog_ubv_to_int_elim.case_0
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo__2b.construct s2 e_v11 (by rw [he_v11]; exact empty_args) hinv2 h64 as ⟨v11, s3, hinv3, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10
  store_step with ih.eo__24eo_5ftypeof s3 v9 _ hinv3 h64 (hG.rem hrem) h_v9 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11
  store_step with ih.eo__24bv_5fbitwidth s4 v12 _ hinv4 h64 (hG.rem hrem) h_v12 as ⟨v13, s5, hinv5, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with Store.builtin_spec_is_neg s5 e_v14 (by rw [he_v14]; rfl) h_v13 hinv5 h64 as ⟨v14, s6, hinv6, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.literal_boolean_spec s6 false hinv6 h64 as ⟨v15, s7, hinv7, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  have h_req_v23 := (show requires_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim s7 v14 v15 v9 ⦃ r s' => s'.Inv ∧ s7.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s7
    req_same v14 v15 with h_v14 h_v15 using hinv7 hG
    req_stuck h_v14 as hq_v14 using hinv7 hG
    step as ⟨e_v16, he_v16⟩
    store_step with CtorSpec.eo__40_40TypedList_2econs.construct s7 e_v16 (by rw [he_v16]; exact empty_args) hinv7 h64 as ⟨v16, s8, hinv8, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s8 0#u32 (0) (by scalar_tac) hinv8 h64 as ⟨v17, s9, hinv9, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
    store_step with ih.eo__24eo_5ftypeof s9 v9 _ hinv9 h64 (hG.rem hrem) h_v9 as ⟨v18, s10, hinv10, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
    store_step with ih.eo__24bv_5fbitwidth s10 v18 _ hinv10 h64 (hG.rem hrem) h_v18 as ⟨v19, s11, hinv11, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
    step as ⟨e_v20, he_v20⟩
    store_step with Store.builtin_spec_list_repeat n ih.eo__24eo_5ftypeof ih.eo__24eo_5fnil s11 e_v20 (by rw [he_v20]; rfl) h_v16 h_v17 h_v19 hinv11 h64 (hG.rem hrem) (by not_left_tac) as ⟨v20, s12, hinv12, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
    try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    store_step with Store.literal_int_u32_spec s12 0#u32 (0) (by scalar_tac) hinv12 h64 as ⟨v21, s13, hinv13, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
    store_step with ih.eo__24iota_5frec s13 v20 v21 _ _ hinv13 h64 (hG.rem hrem) h_v20 h_v21 as ⟨v22, s14, hinv14, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
    req_done hinv14 hG with h_v22 using hq_v14)
  store_step with h_req_v23 as ⟨v23, s15, hinv15, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 1#u32 (1) (by scalar_tac) hinv15 h64 as ⟨v24, s16, hinv16, h_v24⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23
  store_step with ih.eo__24abconv_5fubv_5fto_5fint_5felim s16 v9 v23 v24 _ _ _ hinv16 h64 (hG.rem hrem) h_v9 h_v23 h_v24 as ⟨v25, s17, hinv17, h_v25⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with Store.builtin_spec_list_singleton_elim n ih.eo__24eo_5fis_5flist_5fnil s17 e_v26 (by rw [he_v26]; rfl) h_v11 h_v25 hinv17 h64 (hG.rem hrem) (by not_left_tac) (by nil_apply_tac) as ⟨v26, s18, hinv18, h_v26⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25
  have h_req_v32 := (show requires_1_eo__24eo_5fprog_5fubv_2dto_2dint_2delim s18 v26 v2 v9 ⦃ r s' => s'.Inv ∧ s18.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold requires_1_eo__24eo_5fprog_5fubv_2dto_2dint_2delim
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s18
    req_same v26 v2 with h_v26 h_v2 using hinv18 hG
    req_stuck h_v26 as hq_v26 using hinv18 hG
    step as ⟨e_v27, he_v27⟩
    store_step with CtorSpec.eo__3d.construct s18 e_v27 (by rw [he_v27]; exact empty_args) hinv18 h64 as ⟨v27, s19, hinv19, h_v27⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25 h_v26
    step as ⟨e_v28, he_v28⟩
    store_step with CtorSpec.eo_ubv_5fto_5fint.construct s19 e_v28 (by rw [he_v28]; exact empty_args) hinv19 h64 as ⟨v28, s20, hinv20, h_v28⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25 h_v26 h_v27
    store_step with Store.apply_rep s20 v28 v9 _ _ hinv20 h64 h_v28 h_v9 (by ns_tac) (by ns_tac) as ⟨v29, s21, hinv21, h_v29⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
    store_step with Store.apply_rep s21 v27 v29 _ _ hinv21 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s22, hinv22, h_v30⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
    store_step with Store.apply_rep s22 v30 v2 _ _ hinv22 h64 h_v30 h_v2 (by ns_tac) (by ns_tac) as ⟨v31, s23, hinv23, h_v31⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
    req_done hinv23 hG with h_v31 using hq_v26)
  store_step with h_req_v32 as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v23 h_v24 h_v25 h_v26
  case_done hinv24 hG with h_v32 in EoCases.__eo_prog_ubv_to_int_elim.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9

/-- logos's `__eo_prog_ubv_to_int_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fubv_2dto_2dint_2delim.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ubv_to_int_elim x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ubv_to_int_elim.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ubv_to_int_elim
  unfold EoCases.__eo_prog_ubv_to_int_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ubv_to_int_elim x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fubv_2dto_2dint_2delim.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_ubv_to_int_elim.case_0

theorem eo__24eo_5fprog_5fubv_2dto_2dint_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fubv_2dto_2dint_2delim.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fubv_2dto_2dint_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ubv_to_int_elim x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_ubv_to_int_range.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_ubv_to_int_range.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange more_2_eo__24eo_5fprog_5fubv_5fto_5fint_5frange more_3_eo__24eo_5fprog_5fubv_5fto_5fint_5frange
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_prog_ubv_to_int_range.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_prog_ubv_to_int_range.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s3 0#u32 (0) (by scalar_tac) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s4 v5 v6 _ _ hinv4 h64 h_v5 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s6 v8 v2 _ _ hinv6 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s7 v7 v9 _ _ hinv7 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s8 v4 v10 _ _ hinv8 h64 h_v4 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_and.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3c.construct s10 e_v13 (by rw [he_v13]; exact empty_args) hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s11 e_v14 (by rw [he_v14]; exact empty_args) hinv11 h64 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s12 v14 v2 _ _ hinv12 h64 h_v14 h_v2 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s13 v13 v15 _ _ hinv13 h64 h_v13 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with ih.eo__24eo_5ftypeof s14 v2 _ hinv14 h64 (hG.rem hrem) h_v2 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with ih.eo__24bv_5fbitwidth s15 v17 _ hinv15 h64 (hG.rem hrem) h_v17 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  step as ⟨e_v19, he_v19⟩
  store_step with Store.builtin_spec_is_z s16 e_v19 (by rw [he_v19]; rfl) h_v18 hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  have h_ite_v33 := (show if_1_eo__24eo_5fprog_5fubv_5fto_5fint_5frange s17 v19 v2 ⦃ r s' => s'.Inv ∧ s17.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24eo_5fprog_5fubv_5fto_5fint_5frange
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s17
    rcases Store.boolean_value_term h_v19 with ⟨hx_20, hbv_20⟩ | ⟨hx_20, hbv_20⟩ | ⟨hx_20, hbv_20⟩
    · ite_branch hbv_20
      store_step with ih.eo__24eo_5ftypeof s17 v2 _ hinv17 h64 (hG.rem hrem) h_v2 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      store_step with ih.eo__24bv_5fbitwidth s18 v20 _ hinv18 h64 (hG.rem hrem) h_v20 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      step as ⟨e_v22, he_v22⟩
      store_step with Store.builtin_spec_is_neg s19 e_v22 (by rw [he_v22]; rfl) h_v21 hinv19 h64 as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      have h_ite_v28 := (show if_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange s20 v22 v2 ⦃ r s' => s'.Inv ∧ s20.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold if_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s20
        rcases Store.boolean_value_term h_v22 with ⟨hx_23, hbv_23⟩ | ⟨hx_23, hbv_23⟩ | ⟨hx_23, hbv_23⟩
        · ite_branch hbv_23
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s20 0#u32 (0) (by scalar_tac) hinv20 h64 as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
          ite_done hinv21 hG with (eo_ite_true_rep _ hx_23 h_v23)
        · ite_branch hbv_23
          try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
          store_step with Store.literal_int_u32_spec s20 2#u32 (2) (by scalar_tac) hinv20 h64 as ⟨v24, s21, hinv21, h_v24⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
          store_step with ih.eo__24eo_5ftypeof s21 v2 _ hinv21 h64 (hG.rem hrem) h_v2 as ⟨v25, s22, hinv22, h_v25⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v24
          store_step with ih.eo__24bv_5fbitwidth s22 v25 _ hinv22 h64 (hG.rem hrem) h_v25 as ⟨v26, s23, hinv23, h_v26⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v24 h_v25
          step as ⟨e_v27, he_v27⟩
          store_step with Store.builtin_spec_pow s23 e_v27 (by rw [he_v27]; rfl) h_v24 h_v26 hinv23 h64 as ⟨v27, s24, hinv24, h_v27⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v24 h_v25 h_v26
          ite_done hinv24 hG with (eo_ite_false_rep _ hx_23 h_v27)
        · ite_branch hbv_23
          ite_stuck hinv20 hG with hx_23)
      store_step with h_ite_v28 as ⟨v28, s21, hinv21, h_v28⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      ite_done hinv21 hG with (eo_ite_true_rep _ hx_20 h_v28)
    · ite_branch hbv_20
      step as ⟨e_v29, he_v29⟩
      store_step with CtorSpec.eo_int_2epow2.construct s17 e_v29 (by rw [he_v29]; exact empty_args) hinv17 h64 as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      store_step with ih.eo__24eo_5ftypeof s18 v2 _ hinv18 h64 (hG.rem hrem) h_v2 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v29
      store_step with ih.eo__24bv_5fbitwidth s19 v30 _ hinv19 h64 (hG.rem hrem) h_v30 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v29 h_v30
      store_step with Store.apply_mk_rep s20 v29 v31 _ _ hinv20 h64 h_v29 h_v31 as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v29 h_v30 h_v31
      ite_done hinv21 hG with (eo_ite_false_rep _ hx_20 h_v32)
    · ite_branch hbv_20
      ite_stuck hinv17 hG with hx_20)
  store_step with h_ite_v33 as ⟨v33, s18, hinv18, h_v33⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s18 v16 v33 _ _ hinv18 h64 h_v16 h_v33 as ⟨v34, s19, hinv19, h_v34⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v33
  store_step with Store.apply_mk_rep s19 v12 v34 _ _ hinv19 h64 h_v12 h_v34 as ⟨v35, s20, hinv20, h_v35⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v33 h_v34
  store_step with Store.literal_boolean_spec s20 true hinv20 h64 as ⟨v36, s21, hinv21, h_v36⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v33 h_v34 h_v35
  store_step with Store.apply_mk_rep s21 v35 v36 _ _ hinv21 h64 h_v35 h_v36 as ⟨v37, s22, hinv22, h_v37⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_mk_rep s22 v11 v37 _ _ hinv22 h64 h_v11 h_v37 as ⟨v38, s23, hinv23, h_v38⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v33 h_v34 h_v35 h_v36 h_v37
  case_done hinv23 hG with h_v38 in EoCases.__eo_prog_ubv_to_int_range.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_prog_ubv_to_int_range` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fubv_5fto_5fint_5frange.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_prog_ubv_to_int_range x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_ubv_to_int_range.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_ubv_to_int_range
  unfold EoCases.__eo_prog_ubv_to_int_range.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_ubv_to_int_range x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fubv_5fto_5fint_5frange.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_prog_ubv_to_int_range.case_0

theorem eo__24eo_5fprog_5fubv_5fto_5fint_5frange_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fubv_5fto_5fint_5frange.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fprog_5fubv_5fto_5fint_5frange
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange s1 a0) (fun s' t => Represents.rep s' t (__eo_prog_ubv_to_int_range x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_same v7 a2 with h_v7 h_a2 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_unapply h_v4 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  pat_same v11 a0 with h_v11 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__3e_3d.construct s3 e_v14 (by rw [he_v14]; exact empty_args) hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v15 a0 _ _ hinv5 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v14 v16 _ _ hinv6 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v17 a1 _ _ hinv7 h64 h_v17 h_a1 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v13 v18 _ _ hinv8 h64 h_v13 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_ite.construct s9 e_v20 (by rw [he_v20]; exact empty_args) hinv9 h64 as ⟨v20, s10, hinv10, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3e_3d.construct s10 e_v21 (by rw [he_v21]; exact empty_args) hinv10 h64 as ⟨v21, s11, hinv11, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.apply_rep s11 v21 a1 _ _ hinv11 h64 h_v21 h_a1 (by ns_tac) (by ns_tac) as ⟨v22, s12, hinv12, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_int_2epow2.construct s12 e_v23 (by rw [he_v23]; exact empty_args) hinv12 h64 as ⟨v23, s13, hinv13, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s13 v23 a2 _ _ hinv13 h64 h_v23 h_a2 (by ns_tac) (by ns_tac) as ⟨v24, s14, hinv14, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s14 v22 v24 _ _ hinv14 h64 h_v22 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s15, hinv15, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s15 v20 v25 _ _ hinv15 h64 h_v20 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s16, hinv16, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.literal_boolean_spec s16 false hinv16 h64 as ⟨v27, s17, hinv17, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  store_step with Store.apply_rep s17 v26 v27 _ _ hinv17 h64 h_v26 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s18, hinv18, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo_ite.construct s18 e_v29 (by rw [he_v29]; exact empty_args) hinv18 h64 as ⟨v29, s19, hinv19, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo__3c.construct s19 e_v30 (by rw [he_v30]; exact empty_args) hinv19 h64 as ⟨v30, s20, hinv20, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s20 v30 a1 _ _ hinv20 h64 h_v30 h_a1 (by ns_tac) (by ns_tac) as ⟨v31, s21, hinv21, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s21 0#u32 (0) (by scalar_tac) hinv21 h64 as ⟨v32, s22, hinv22, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s22 v31 v32 _ _ hinv22 h64 h_v31 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s23, hinv23, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s23 v29 v33 _ _ hinv23 h64 h_v29 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s24, hinv24, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.literal_boolean_spec s24 true hinv24 h64 as ⟨v35, s25, hinv25, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s25 v34 v35 _ _ hinv25 h64 h_v34 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s26, hinv26, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_bvuge.construct s26 e_v37 (by rw [he_v37]; exact empty_args) hinv26 h64 as ⟨v37, s27, hinv27, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s27 v37 a0 _ _ hinv27 h64 h_v37 h_a0 (by ns_tac) (by ns_tac) as ⟨v38, s28, hinv28, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s28 e_v39 (by rw [he_v39]; rfl) h_a2 hinv28 h64 as ⟨v39, s29, hinv29, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s29 v39 a1 _ _ hinv29 h64 h_v39 h_a1 (by ns_tac) (by ns_tac) as ⟨v40, s30, hinv30, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s30 v38 v40 _ _ hinv30 h64 h_v38 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s31, hinv31, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s31 v36 v41 _ _ hinv31 h64 h_v36 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s32, hinv32, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s32 v28 v42 _ _ hinv32 h64 h_v28 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s33, hinv33, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s33 v19 v43 _ _ hinv33 h64 h_v19 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s34, hinv34, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  case_done hinv34 hG with h_v44 in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_uf_bv2nat_geq_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_geq_elim
  unfold EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_bv2nat_geq_elim.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_geq_elim x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dgeq_2delim_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a2 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40bvsize.construct s1 e_v12 (by rw [he_v12]; exact empty_args) hinv1 h64 as ⟨v12, s2, hinv2, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11
  pat_same v10 v12 with h_v10 h_v12 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_same v11 a1 with h_v11 h_a1 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  pat_same v4 a0 with h_v4 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v13 (by rw [he_v13]; exact empty_args) hinv2 h64 as ⟨v13, s3, hinv3, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s3 e_v14 (by rw [he_v14]; rfl) h_a0 hinv3 h64 as ⟨v14, s4, hinv4, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s4 e_v15 (by rw [he_v15]; exact empty_args) hinv4 h64 as ⟨v15, s5, hinv5, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s5 v15 a1 _ _ hinv5 h64 h_v15 h_a1 (by ns_tac) (by ns_tac) as ⟨v16, s6, hinv6, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s6 v14 v16 _ _ hinv6 h64 h_v14 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s7, hinv7, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s7 v13 v17 _ _ hinv7 h64 h_v13 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s8, hinv8, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s8 v18 a1 _ _ hinv8 h64 h_v18 h_a1 (by ns_tac) (by ns_tac) as ⟨v19, s9, hinv9, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  case_done hinv9 hG with h_v19 in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 using hn_a0 hn_a1 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11

/-- logos's `__eo_prog_uf_bv2nat_int2bv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_int2bv.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_int2bv
  unfold EoCases.__eo_prog_uf_bv2nat_int2bv.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_bv2nat_int2bv.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v35 a0 with h_v35 h_a0 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_unapply h_v32 as ⟨v38, v39, x_v38, x_v39, h_v38, h_v39, hn_v38, hn_v39⟩ using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo__40bvsize.construct s6 e_v40 (by rw [he_v40]; exact empty_args) hinv6 h64 as ⟨v40, s7, hinv7, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39
  pat_same v38 v40 with h_v38 h_v40 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  pat_same v39 a1 with h_v39 h_a1 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v41 (by rw [he_v41]; exact empty_args) hinv7 h64 as ⟨v41, s8, hinv8, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v42 (by rw [he_v42]; rfl) h_a0 hinv8 h64 as ⟨v42, s9, hinv9, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v43 (by rw [he_v43]; exact empty_args) hinv9 h64 as ⟨v43, s10, hinv10, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s10 v43 a1 _ _ hinv10 h64 h_v43 h_a1 (by ns_tac) (by ns_tac) as ⟨v44, s11, hinv11, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s11 v42 v44 _ _ hinv11 h64 h_v42 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s12, hinv12, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s12 v41 v45 _ _ hinv12 h64 h_v41 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s13, hinv13, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo_concat.construct s13 e_v47 (by rw [he_v47]; exact empty_args) hinv13 h64 as ⟨v47, s14, hinv14, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  step as ⟨e_v48, he_v48⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s14 e_v48 (by rw [he_v48]; rfl) h_a2 hinv14 h64 as ⟨v48, s15, hinv15, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s15 0#u32 (0) (by scalar_tac) hinv15 h64 as ⟨v49, s16, hinv16, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s16 v48 v49 _ _ hinv16 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s17, hinv17, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with Store.apply_rep s17 v47 v50 _ _ hinv17 h64 h_v47 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s18, hinv18, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo_concat.construct s18 e_v52 (by rw [he_v52]; exact empty_args) hinv18 h64 as ⟨v52, s19, hinv19, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  store_step with Store.apply_rep s19 v52 a1 _ _ hinv19 h64 h_v52 h_a1 (by ns_tac) (by ns_tac) as ⟨v53, s20, hinv20, h_v53⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s20 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv20 h64 as ⟨v54, s21, hinv21, h_v54⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53
  store_step with Store.apply_rep s21 v53 v54 _ _ hinv21 h64 h_v53 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s22, hinv22, h_v55⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54
  store_step with Store.apply_rep s22 v51 v55 _ _ hinv22 h64 h_v51 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s23, hinv23, h_v56⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55
  store_step with Store.apply_rep s23 v46 v56 _ _ hinv23 h64 h_v46 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s24, hinv24, h_v57⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51 h_v52 h_v53 h_v54 h_v55 h_v56
  case_done hinv24 hG with h_v57 in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35 hn_v38 hn_v39

/-- logos's `__eo_prog_uf_bv2nat_int2bv_extend` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_int2bv_extend
  unfold EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_bv2nat_int2bv_extend.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extend x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextend_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract more_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract more_1_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract more_2_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a3 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v1 as ⟨v3, v4, x_v3, x_v4, h_v3, h_v4, hn_v3, hn_v4⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v3 as ⟨v6, v7, x_v6, x_v7, h_v6, h_v7, hn_v6, hn_v7⟩ using hinv else hinv hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s e_v8 (by rw [he_v8]; exact empty_args) hinv h64 as ⟨v8, s1, hinv1, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7
  pat_same v6 v8 with h_v6 h_v8 using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v7 as ⟨v10, v11, x_v10, x_v11, h_v10, h_v11, hn_v10, hn_v11⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v10 as ⟨v13, v14, x_v13, x_v14, h_v13, h_v14, hn_v13, hn_v14⟩ using hinv1 else hinv1 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v15 (by rw [he_v15]; exact empty_args) hinv1 h64 as ⟨v15, s2, hinv2, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14
  pat_same v13 v15 with h_v13 h_v15 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v14 a0 with h_v14 h_a0 using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v11 as ⟨v17, v18, x_v17, x_v18, h_v17, h_v18, hn_v17, hn_v18⟩ using hinv2 else hinv2 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40bvsize.construct s2 e_v19 (by rw [he_v19]; exact empty_args) hinv2 h64 as ⟨v19, s3, hinv3, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18
  pat_same v17 v19 with h_v17 h_v19 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v18 a1 with h_v18 h_a1 using hinv3 else hinv3 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v20, s4, hinv4, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19
  pat_same v4 v20 with h_v4 h_v20 using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_destruct CtorSpec.eo__24eo_5fpf.destruct h_a4 as ⟨v22, x_v22, h_v22⟩ else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v22 as ⟨v24, v25, x_v24, x_v25, h_v24, h_v25, hn_v24, hn_v25⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v24 as ⟨v27, v28, x_v27, x_v28, h_v27, h_v28, hn_v27, hn_v28⟩ using hinv4 else hinv4 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v29 (by rw [he_v29]; exact empty_args) hinv4 h64 as ⟨v29, s5, hinv5, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28
  pat_same v27 v29 with h_v27 h_v29 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v28 a2 with h_v28 h_a2 using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v25 as ⟨v31, v32, x_v31, x_v32, h_v31, h_v32, hn_v31, hn_v32⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_unapply h_v31 as ⟨v34, v35, x_v34, x_v35, h_v34, h_v35, hn_v34, hn_v35⟩ using hinv5 else hinv5 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__2d.construct s5 e_v36 (by rw [he_v36]; exact empty_args) hinv5 h64 as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35
  pat_same v34 v36 with h_v34 h_v36 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  pat_same v35 a0 with h_v35 h_a0 using hinv6 else hinv6 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s6 1#u32 (1) (by scalar_tac) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36
  pat_same v32 v37 with h_v32 h_v37 using hinv7 else hinv7 hG in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v38 (by rw [he_v38]; exact empty_args) hinv7 h64 as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s8 e_v39 (by rw [he_v39]; rfl) h_a0 hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v40 (by rw [he_v40]; exact empty_args) hinv9 h64 as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s10 v40 a1 _ _ hinv10 h64 h_v40 h_a1 (by ns_tac) (by ns_tac) as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s11 v39 v41 _ _ hinv11 h64 h_v39 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s12, hinv12, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.apply_rep s12 v38 v42 _ _ hinv12 h64 h_v38 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s13, hinv13, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s13 0#u32 (0) (by scalar_tac) hinv13 h64 as ⟨v44, s14, hinv14, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo_extract.construct s14 e_v45 (by rw [he_v45]; rfl) h_a2 h_v44 hinv14 h64 as ⟨v45, s15, hinv15, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s15 v45 a1 _ _ hinv15 h64 h_v45 h_a1 (by ns_tac) (by ns_tac) as ⟨v46, s16, hinv16, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  store_step with Store.apply_rep s16 v43 v46 _ _ hinv16 h64 h_v43 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s17, hinv17, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v1 h_v3 h_v4 h_v6 h_v7 h_v8 h_v10 h_v11 h_v13 h_v14 h_v15 h_v17 h_v18 h_v19 h_v20 h_v22 h_v24 h_v25 h_v27 h_v28 h_v29 h_v31 h_v32 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  case_done hinv17 hG with h_v47 in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 using hn_a0 hn_a1 hn_a2 hn_v3 hn_v4 hn_v6 hn_v7 hn_v10 hn_v11 hn_v13 hn_v14 hn_v17 hn_v18 hn_v24 hn_v25 hn_v27 hn_v28 hn_v31 hn_v32 hn_v34 hn_v35

/-- logos's `__eo_prog_uf_bv2nat_int2bv_extract` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_bv2nat_int2bv_extract
  unfold EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) :
    body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__eo_prog_uf_bv2nat_int2bv_extract.case_0

theorem eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4
  unfold eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_prog_uf_bv2nat_int2bv_extract x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dbv2nat_2dint2bv_2dextract_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo_int_5fto_5fbv.construct s2 e_v2 (by rw [he_v2]; rfl) h_a0 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v1 v3 _ _ hinv4 h64 h_v1 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s5 v0 v4 _ _ hinv5 h64 h_v0 h_v4 (by ns_tac) (by ns_tac) as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a1 _ _ hinv7 h64 h_v6 h_a1 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_int_2epow2.construct s8 e_v8 (by rw [he_v8]; exact empty_args) hinv8 h64 as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s9 v8 a0 _ _ hinv9 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v7 v9 _ _ hinv10 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v5 v10 _ _ hinv11 h64 h_v5 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv12 hG with h_v11 in EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_uf_int2bv_bv2nat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_uf_int2bv_bv2nat x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_int2bv_bv2nat.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_int2bv_bv2nat
  unfold EoCases.__eo_prog_uf_int2bv_bv2nat.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bv2nat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_int2bv_bv2nat.case_0

theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_uf_int2bv_bv2nat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dint2bv_2dbv2nat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvule.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3c_3d.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_uf_int2bv_bvule_equiv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_int2bv_bvule_equiv
  unfold EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_int2bv_bvule_equiv.case_0

theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_uf_int2bv_bvule_equiv x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvule_2dequiv_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv more_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_bvult.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  store_step with Store.apply_rep s2 v1 a0 _ _ hinv2 h64 h_v1 h_a0 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a1 _ _ hinv3 h64 h_v2 h_a1 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v0 v3 _ _ hinv4 h64 h_v0 h_v3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3c.construct s5 e_v5 (by rw [he_v5]; exact empty_args) hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s6 e_v6 (by rw [he_v6]; exact empty_args) hinv6 h64 as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v6 a0 _ _ hinv7 h64 h_v6 h_a0 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s8 v5 v7 _ _ hinv8 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s9, hinv9, h_v8⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ubv_5fto_5fint.construct s9 e_v9 (by rw [he_v9]; exact empty_args) hinv9 h64 as ⟨v9, s10, hinv10, h_v9⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s10 v9 a1 _ _ hinv10 h64 h_v9 h_a1 (by ns_tac) (by ns_tac) as ⟨v10, s11, hinv11, h_v10⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s11 v8 v10 _ _ hinv11 h64 h_v8 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s12, hinv12, h_v11⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s12 v4 v11 _ _ hinv12 h64 h_v4 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s13, hinv13, h_v12⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv13 hG with h_v12 in EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 using hn_a0 hn_a1

/-- logos's `__eo_prog_uf_int2bv_bvult_equiv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_prog_uf_int2bv_bvult_equiv
  unfold EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0
  logos_eq

theorem body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  body_stuck hinv1 hG using hn_a0 hn_a1 hc0 in EoCases.__eo_prog_uf_int2bv_bvult_equiv.case_0

theorem eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_prog_uf_int2bv_bvult_equiv x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fprog_5fuf_2dint2bv_2dbvult_2dequiv_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
