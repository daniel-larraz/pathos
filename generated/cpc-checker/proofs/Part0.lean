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

theorem case_0_eo__24abconv_5fint_5fto_5fbv_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24abconv_5fint_5fto_5fbv_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__abconv_int_to_bv_elim.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__abconv_int_to_bv_elim.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24abconv_5fint_5fto_5fbv_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__abconv_int_to_bv_elim.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a1 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__abconv_int_to_bv_elim.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__abconv_int_to_bv_elim.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v2 h_v4 hinv2 s2 v2 v4
  case_done hinv3 hG with h_v5 in EoCases.__abconv_int_to_bv_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_1_eo__24abconv_5fint_5fto_5fbv_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24abconv_5fint_5fto_5fbv_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__abconv_int_to_bv_elim.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__abconv_int_to_bv_elim.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24abconv_5fint_5fto_5fbv_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__abconv_int_to_bv_elim.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__abconv_int_to_bv_elim.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__abconv_int_to_bv_elim.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 dropping h_v4 h_v6 hinv1 s1 v4 v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__abconv_int_to_bv_elim.case_1
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_concat.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_v5 h_v7 he_v8 hinv2 e_v8 s2 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 dropping he_v9 hinv3 e_v9 s3
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo__3e_3d.construct s4 e_v10 (by rw [he_v10]; exact empty_args) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 dropping he_v10 hinv4 e_v10 s4
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s5 e_v11 (by rw [he_v11]; exact empty_args) hinv5 h64 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 h_v10 dropping he_v11 hinv5 e_v11 s5
  store_step with Store.apply_rep s6 v11 a0 _ _ hinv6 h64 h_v11 h_a0 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 h_v10 dropping h_v11 hinv6 s6 v11
  store_step with Store.apply_rep s7 v12 a2 _ _ hinv7 h64 h_v12 h_a2 (by ns_tac) (by ns_tac) as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 h_v10 dropping h_v12 hinv7 s7 v12
  store_step with Store.apply_rep s8 v10 v13 _ _ hinv8 h64 h_v10 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 dropping h_v10 h_v13 hinv8 s8 v10 v13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 2#u32 (2) (by scalar_tac) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 h_v14 dropping hinv9 s9
  step as ⟨e_v16, he_v16⟩
  store_step with Store.builtin_spec_int_div s10 e_v16 (by rw [he_v16]; rfl) h_a2 h_v15 hinv10 h64 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 h_v14 dropping h_v15 he_v16 hinv10 e_v16 s10 v15
  store_step with Store.apply_mk_rep s11 v14 v16 _ _ hinv11 h64 h_v14 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v9 dropping h_v14 h_v16 hinv11 s11 v14 v16
  store_step with Store.apply_mk_rep s12 v9 v17 _ _ hinv12 h64 h_v9 h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 dropping h_v17 h_v9 hinv12 s12 v17 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s13 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v18 dropping hinv13 s13
  store_step with Store.apply_mk_rep s14 v18 v19 _ _ hinv14 h64 h_v18 h_v19 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 dropping h_v18 h_v19 hinv14 s14 v18 v19
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s15 1#u32 0#u32 (1) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 h_v20 dropping hinv15 s15
  store_step with Store.apply_mk_rep s16 v20 v21 _ _ hinv16 h64 h_v20 h_v21 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a2 h_v2 h_v8 dropping h_v20 h_v21 hinv16 s16 v20 v21
  store_step with Store.apply_mk_rep s17 v8 v22 _ _ hinv17 h64 h_v8 h_v22 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_v22 h_v8 hinv17 s17 v22 v8
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 2#u32 (2) (by scalar_tac) hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_a0 h_a2 h_v2 h_v23 dropping hinv18 s18
  step as ⟨e_v25, he_v25⟩
  store_step with Store.builtin_spec_int_div s19 e_v25 (by rw [he_v25]; rfl) h_a2 h_v24 hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_a0 h_v2 h_v23 dropping h_a2 h_v24 he_v25 hinv19 e_v25 s19 v24
  store_step with ih.eo__24abconv_5fint_5fto_5fbv_5felim s20 a0 v2 v25 _ _ _ hinv20 h64 (hG.rem hrem) h_a0 h_v2 h_v25 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v23 dropping h_a0 h_v2 h_v25 hinv20 s20 v2 v25
  store_step with Store.apply_mk_rep s21 v23 v26 _ _ hinv21 h64 h_v23 h_v26 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying dropping h_v23 h_v26 hinv21 s21 v23 v26
  case_done hinv22 hG with h_v27 in EoCases.__abconv_int_to_bv_elim.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__abconv_int_to_bv_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24abconv_5fint_5fto_5fbv_5felim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __abconv_int_to_bv_elim x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__abconv_int_to_bv_elim.case_0 x_a0 x_a1 x_a2, EoCases.__abconv_int_to_bv_elim.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __abconv_int_to_bv_elim
  unfold EoCases.__abconv_int_to_bv_elim.case_0 EoCases.__abconv_int_to_bv_elim.case_1
  logos_eq

theorem body_eo__24abconv_5fint_5fto_5fbv_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24abconv_5fint_5fto_5fbv_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__abconv_int_to_bv_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24abconv_5fint_5fto_5fbv_5felim.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24abconv_5fint_5fto_5fbv_5felim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24abconv_5fint_5fto_5fbv_5felim_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24abconv_5fint_5fto_5fbv_5felim_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__abconv_int_to_bv_elim.case_0 EoCases.__abconv_int_to_bv_elim.case_1

theorem eo__24abconv_5fint_5fto_5fbv_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24abconv_5fint_5fto_5fbv_5felim.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24abconv_5fint_5fto_5fbv_5felim
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 0#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24abconv_5fint_5fto_5fbv_5felim s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__abconv_int_to_bv_elim x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_0 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_0 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24abconv_5fint_5fto_5fbv_5felim_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24abconv_5fubv_5fto_5fint_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24abconv_5fubv_5fto_5fint_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__abconv_ubv_to_int_elim.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__abconv_ubv_to_int_elim.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24abconv_5fubv_5fto_5fint_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__abconv_ubv_to_int_elim.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a1 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__abconv_ubv_to_int_elim.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__abconv_ubv_to_int_elim.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying dropping h_v2 h_v4 hinv2 s2 v2 v4
  case_done hinv3 hG with h_v5 in EoCases.__abconv_ubv_to_int_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_1_eo__24abconv_5fubv_5fto_5fint_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24abconv_5fubv_5fto_5fint_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__abconv_ubv_to_int_elim.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__abconv_ubv_to_int_elim.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24abconv_5fubv_5fto_5fint_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__abconv_ubv_to_int_elim.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__abconv_ubv_to_int_elim.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__abconv_ubv_to_int_elim.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_extract.construct s4 e_v10 (by rw [he_v10]; rfl) h_v5 h_v5 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v8 h_v9 dropping h_v5 he_v10 hinv4 e_v10 s4 v5
  store_step with Store.apply_rep s5 v10 a0 _ _ hinv5 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v8 h_v9 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v9 v11 _ _ hinv6 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v8 dropping h_v11 h_v9 hinv6 s6 v11 v9
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s7 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v8 h_v12 dropping hinv7 s7
  store_step with Store.apply_rep s8 v12 v13 _ _ hinv8 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v8 dropping h_v12 h_v13 hinv8 s8 v12 v13
  store_step with Store.apply_rep s9 v8 v14 _ _ hinv9 h64 h_v8 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 dropping h_v14 h_v8 hinv9 s9 v14 v8
  store_step with Store.apply_rep s10 v15 a2 _ _ hinv10 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 dropping h_v15 hinv10 s10 v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 h_v16 dropping hinv11 s11
  store_step with Store.apply_rep s12 v16 v17 _ _ hinv12 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a2 h_v2 h_v7 dropping h_v16 h_v17 hinv12 s12 v16 v17
  store_step with Store.apply_rep s13 v7 v18 _ _ hinv13 h64 h_v7 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_v18 h_v7 hinv13 s13 v18 v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 2#u32 (2) (by scalar_tac) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a2 h_v2 h_v19 dropping hinv14 s14
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_mul s15 e_v21 (by rw [he_v21]; rfl) h_a2 h_v20 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_v2 h_v19 dropping h_a2 h_v20 he_v21 hinv15 e_v21 s15 v20
  store_step with ih.eo__24abconv_5fubv_5fto_5fint_5felim s16 a0 v2 v21 _ _ _ hinv16 h64 (hG.rem hrem) h_a0 h_v2 h_v21 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v19 dropping h_a0 h_v2 h_v21 hinv16 s16 v2 v21
  store_step with Store.apply_mk_rep s17 v19 v22 _ _ hinv17 h64 h_v19 h_v22 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying dropping h_v19 h_v22 hinv17 s17 v19 v22
  case_done hinv18 hG with h_v23 in EoCases.__abconv_ubv_to_int_elim.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__abconv_ubv_to_int_elim` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24abconv_5fubv_5fto_5fint_5felim.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __abconv_ubv_to_int_elim x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__abconv_ubv_to_int_elim.case_0 x_a0 x_a1 x_a2, EoCases.__abconv_ubv_to_int_elim.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __abconv_ubv_to_int_elim
  unfold EoCases.__abconv_ubv_to_int_elim.case_0 EoCases.__abconv_ubv_to_int_elim.case_1
  logos_eq

theorem body_eo__24abconv_5fubv_5fto_5fint_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24abconv_5fubv_5fto_5fint_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__abconv_ubv_to_int_elim x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24abconv_5fubv_5fto_5fint_5felim.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24abconv_5fubv_5fto_5fint_5felim
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24abconv_5fubv_5fto_5fint_5felim_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24abconv_5fubv_5fto_5fint_5felim_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__abconv_ubv_to_int_elim.case_0 EoCases.__abconv_ubv_to_int_elim.case_1

theorem eo__24abconv_5fubv_5fto_5fint_5felim_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24abconv_5fubv_5fto_5fint_5felim.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24abconv_5fubv_5fto_5fint_5felim
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 1#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24abconv_5fubv_5fto_5fint_5felim s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__abconv_ubv_to_int_elim x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_1 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_1 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24abconv_5fubv_5fto_5fint_5felim_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24are_5fdistinct_5fterms_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24are_5fdistinct_5fterms_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_list.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_list.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24are_5fdistinct_5fterms_5flist
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_list.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a1 h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_list.case_0
  pat_same a1 v2 with h_a1 h_v2 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_list.case_0
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_a1 h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  case_done hinv2 hG with h_v4 in EoCases.__are_distinct_terms_list.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24are_5fdistinct_5fterms_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24are_5fdistinct_5fterms_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_list.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_list.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24are_5fdistinct_5fterms_5flist
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_list.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_list.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a1 h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_list.case_1
  store_step with ih.eo__24are_5fdistinct_5fterms_5flist_5frec s1 v5 v2 a1 _ _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v2 h_a1 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a1 h_v2 dropping h_v4 h_v5 h_v6 hinv1 s1 v4 v5 v6
  have h_ite_v10 := (show if_0_eo__24are_5fdistinct_5fterms_5flist s2 v7 v2 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24are_5fdistinct_5fterms_5flist
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with ih.eo__24are_5fdistinct_5fterms_5flist s2 v2 a1 _ _ hinv2 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying dropping h_a1 h_v2 h_v7 v2 v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying dropping h_a1 h_v2 h_v7 v2 v7
      ite_done hinv3 hG with (eo_ite_false_rep _ hx_8 h_v9)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v10 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying dropping h_a1 h_ite_v10 h_v2 h_v7 hinv2 s2 v2 v7
  case_done hinv3 hG with h_v10 in EoCases.__are_distinct_terms_list.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's fall-through helpers of `__are_distinct_terms_list`, each the program's cases from its first on. -/
theorem eo__24are_5fdistinct_5fterms_5flist.helper_1 (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    Eo.__eo_l_1___are_distinct_terms_list x_a0 x_a1 =
      firstSome [EoCases.__are_distinct_terms_list.case_1 x_a0 x_a1] HasStuck.stuck := by
  conv => lhs; unfold Eo.__eo_l_1___are_distinct_terms_list
  unfold EoCases.__are_distinct_terms_list.case_1
  logos_eq_deep

/-- logos's `__are_distinct_terms_list` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24are_5fdistinct_5fterms_5flist.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __are_distinct_terms_list x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__are_distinct_terms_list.case_0 x_a0 x_a1, EoCases.__are_distinct_terms_list.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __are_distinct_terms_list
  unfold EoCases.__are_distinct_terms_list.case_0
  have hn := eo__24are_5fdistinct_5fterms_5flist.helper_1
  logos_eq_deep

theorem body_eo__24are_5fdistinct_5fterms_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24are_5fdistinct_5fterms_5flist s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__are_distinct_terms_list x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24are_5fdistinct_5fterms_5flist.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24are_5fdistinct_5fterms_5flist
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24are_5fdistinct_5fterms_5flist_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24are_5fdistinct_5fterms_5flist_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__are_distinct_terms_list.case_0 EoCases.__are_distinct_terms_list.case_1

theorem eo__24are_5fdistinct_5fterms_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24are_5fdistinct_5fterms_5flist.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24are_5fdistinct_5fterms_5flist
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 3#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24are_5fdistinct_5fterms_5flist s1 a0 a1) (fun s' t => Represents.rep s' t (__are_distinct_terms_list x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_3 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_3 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24are_5fdistinct_5fterms_5flist_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24are_5fdistinct_5fterms_5flist_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24are_5fdistinct_5fterms_5flist_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_list_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_list_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24are_5fdistinct_5fterms_5flist_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_list_rec.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_list_rec.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a2 h_v2 h_v4 h_v5 dropping h_a1 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_list_rec.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_eq s1 e_v7 (by rw [he_v7]; rfl) h_a0 h_v5 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  have h_ite_v10 := (show if_0_eo__24are_5fdistinct_5fterms_5flist_5frec s2 v7 a0 v5 a2 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24are_5fdistinct_5fterms_5flist_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v7 with ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩ | ⟨hx_8, hbv_8⟩
    · ite_branch hbv_8
      store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a2 h_v2 h_v5 dropping h_v7 v7
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_8 h_v8)
    · ite_branch hbv_8
      store_step with ih.eo__24are_5fdistinct_5fterms_5ftype s2 a0 v5 a2 _ _ _ hinv2 h64 (hG.rem hrem) h_a0 h_v5 h_a2 as ⟨v9, s3, hinv3, h_v9⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_v5 h_v7 v5 v7
      ite_done hinv3 hG with (eo_ite_false_rep _ hx_8 h_v9)
    · ite_branch hbv_8
      ite_stuck hinv2 hG with hx_8)
  store_step with h_ite_v10 as ⟨v10, s3, hinv3, h_v10⟩ growing hG carrying h_a0 h_a2 h_v2 dropping h_ite_v10 h_v5 h_v7 hinv2 s2 v5 v7
  have h_ite_v13 := (show if_1_eo__24are_5fdistinct_5fterms_5flist_5frec s3 v10 a0 v2 a2 ⦃ r s' => s'.Inv ∧ s3.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24are_5fdistinct_5fterms_5flist_5frec
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s3
    rcases Store.boolean_value_term h_v10 with ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩ | ⟨hx_11, hbv_11⟩
    · ite_branch hbv_11
      store_step with ih.eo__24are_5fdistinct_5fterms_5flist_5frec s3 a0 v2 a2 _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v2 h_a2 as ⟨v11, s4, hinv4, h_v11⟩ growing hG carrying dropping h_a0 h_a2 h_v10 h_v2 v10 v2
      ite_done hinv4 hG with (eo_ite_true_rep _ hx_11 h_v11)
    · ite_branch hbv_11
      store_step with Store.literal_boolean_spec s3 false hinv3 h64 as ⟨v12, s4, hinv4, h_v12⟩ growing hG carrying dropping h_a0 h_v10 h_v2 v10 v2
      ite_done hinv4 hG with (eo_ite_false_rep _ hx_11 h_v12)
    · ite_branch hbv_11
      ite_stuck hinv3 hG with hx_11)
  store_step with h_ite_v13 as ⟨v13, s4, hinv4, h_v13⟩ growing hG carrying dropping h_a0 h_ite_v13 h_v10 h_v2 hinv3 s3 v10 v2
  case_done hinv4 hG with h_v13 in EoCases.__are_distinct_terms_list_rec.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24are_5fdistinct_5fterms_5flist_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24are_5fdistinct_5fterms_5flist_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_list_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_list_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24are_5fdistinct_5fterms_5flist_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_list_rec.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a2 h_v1 h_v2 dropping h_a1 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_list_rec.case_1
  pat_same a2 v2 with h_a2 h_v2 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_list_rec.case_1
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_a2 h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  case_done hinv2 hG with h_v4 in EoCases.__are_distinct_terms_list_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__are_distinct_terms_list_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24are_5fdistinct_5fterms_5flist_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __are_distinct_terms_list_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__are_distinct_terms_list_rec.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_list_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __are_distinct_terms_list_rec
  unfold EoCases.__are_distinct_terms_list_rec.case_0 EoCases.__are_distinct_terms_list_rec.case_1
  logos_eq

theorem body_eo__24are_5fdistinct_5fterms_5flist_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24are_5fdistinct_5fterms_5flist_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__are_distinct_terms_list_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24are_5fdistinct_5fterms_5flist_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24are_5fdistinct_5fterms_5flist_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24are_5fdistinct_5fterms_5flist_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24are_5fdistinct_5fterms_5flist_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__are_distinct_terms_list_rec.case_0 EoCases.__are_distinct_terms_list_rec.case_1

theorem eo__24are_5fdistinct_5fterms_5flist_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24are_5fdistinct_5fterms_5flist_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24are_5fdistinct_5fterms_5flist_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 4#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24are_5fdistinct_5fterms_5flist_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__are_distinct_terms_list_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_4 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_4 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24are_5fdistinct_5fterms_5flist_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_z s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_a2 h_v0 he_v1 hinv1 e_v1 s1 v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_is_z s2 e_v2 (by rw [he_v2]; rfl) h_a1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v1 dropping h_a1 he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_and s3 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_v1 h_v2 he_v3 hinv3 e_v3 s3 v1 v2
  case_done hinv4 hG with h_v3 in EoCases.__are_distinct_terms_type.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_q s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_a2 h_v0 he_v1 hinv1 e_v1 s1 v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_is_q s2 e_v2 (by rw [he_v2]; rfl) h_a1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v1 dropping h_a1 he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_and s3 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_v1 h_v2 he_v3 hinv3 e_v3 s3 v1 v2
  case_done hinv4 hG with h_v3 in EoCases.__are_distinct_terms_type.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_type.case_2
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 dropping h_a2 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Char.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__are_distinct_terms_type.case_2
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_is_str s2 e_v5 (by rw [he_v5]; rfl) h_a0 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a1 dropping h_a0 h_v2 h_v4 he_v5 hinv2 e_v5 s2 v2 v4
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_is_str s3 e_v6 (by rw [he_v6]; rfl) h_a1 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v5 dropping h_a1 he_v6 hinv3 e_v6 s3
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_and s4 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying dropping h_v5 h_v6 he_v7 hinv4 e_v7 s4 v5 v6
  case_done hinv5 hG with h_v7 in EoCases.__are_distinct_terms_type.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_3_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_type.case_3
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 dropping h_a2 h_v2 he_v3 e_v3 v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_3
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_is_bin s1 e_v4 (by rw [he_v4]; rfl) h_a0 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a1 dropping h_a0 h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_is_bin s2 e_v5 (by rw [he_v5]; rfl) h_a1 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping h_a1 he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_and s3 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 h_v5 he_v6 hinv3 e_v6 s3 v4 v5
  case_done hinv4 hG with h_v6 in EoCases.__are_distinct_terms_type.case_3 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_4_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_4_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fBool.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_bool s1 e_v1 (by rw [he_v1]; rfl) h_a0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 dropping h_a0 h_a2 h_v0 he_v1 hinv1 e_v1 s1 v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_is_bool s2 e_v2 (by rw [he_v2]; rfl) h_a1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_v1 dropping h_a1 he_v2 hinv2 e_v2 s2
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_and s3 e_v3 (by rw [he_v3]; rfl) h_v1 h_v2 hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_v1 h_v2 he_v3 hinv3 e_v3 s3 v1 v2
  case_done hinv4 hG with h_v3 in EoCases.__are_distinct_terms_type.case_4 using hn_a0 hn_a1 hn_a2

theorem case_5_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_5_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_type.case_5
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Set.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 dropping h_a2 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_5
  store_step with ih.eo__24set_5fis_5fnot_5fsubset s1 a0 a1 v2 _ _ _ hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v2 dropping h_v1 h_v3 hinv1 s1 v1 v3
  store_step with ih.eo__24set_5fis_5fnot_5fsubset s2 a1 a0 v2 _ _ _ hinv2 h64 (hG.rem hrem) h_a1 h_a0 h_v2 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v4 dropping h_a0 h_a1 h_v2 hinv2 s2 v2
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_or s3 e_v6 (by rw [he_v6]; rfl) h_v4 h_v5 hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying dropping h_v4 h_v5 he_v6 hinv3 e_v6 s3 v4 v5
  case_done hinv4 hG with h_v6 in EoCases.__are_distinct_terms_type.case_5 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_6_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_6_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__are_distinct_terms_type.case_6
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 dropping h_a2 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__are_distinct_terms_type.case_6
  store_step with ih.eo__24seq_5fdistinct_5fterms s1 a0 a1 v2 _ _ _ hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_v2 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying dropping h_a0 h_a1 h_v1 h_v2 h_v3 hinv1 s1 v1 v2 v3
  case_done hinv2 hG with h_v4 in EoCases.__are_distinct_terms_type.case_6 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_7_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_7_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  store_step with ih.eo__24dt_5fdistinct_5fterms s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 dropping
  step as ⟨e_v1, he_v1⟩
  store_step with Store.builtin_spec_is_ok s1 e_v1 (by rw [he_v1]; rfl) h_v0 hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 dropping h_v0 he_v1 hinv1 e_v1 s1 v0
  have h_ite_v4 := (show if_0_eo__24are_5fdistinct_5fterms_5ftype s2 v1 a0 a1 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24are_5fdistinct_5fterms_5ftype
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_v1 with ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩ | ⟨hx_2, hbv_2⟩
    · ite_branch hbv_2
      store_step with ih.eo__24dt_5fdistinct_5fterms s2 a0 a1 _ _ hinv2 h64 (hG.rem hrem) h_a0 h_a1 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying dropping h_a0 h_a1 h_v1 v1
      ite_done hinv3 hG with (eo_ite_true_rep _ hx_2 h_v2)
    · ite_branch hbv_2
      store_step with Store.literal_boolean_spec s2 false hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying dropping h_a0 h_a1 h_v1 v1
      ite_done hinv3 hG with (eo_ite_false_rep _ hx_2 h_v3)
    · ite_branch hbv_2
      ite_stuck hinv2 hG with hx_2)
  store_step with h_ite_v4 as ⟨v4, s3, hinv3, h_v4⟩ growing hG carrying dropping h_a0 h_a1 h_ite_v4 h_v1 hinv2 s2 v1
  case_done hinv3 hG with h_v4 in EoCases.__are_distinct_terms_type.case_7 using hn_a0 hn_a1 hn_a2

theorem cases_0_0_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2 = none ∧ EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2 = none ∧ EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2 = none ∧ EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] = [] ++ [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2
  group_step with case_1_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hl_0
  group_step with case_2_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1
  group_step with case_3_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2 = none ∧ EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2 = none ∧ EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2 = none ∧ EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] = [] ++ [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2
  group_step with case_5_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hn_a2 hl_4
  group_step with case_6_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hn_a1 hn_a2 hl_4 hl_5
  group_step with case_7_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hn_a1 hn_a2 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

/-- logos's `__are_distinct_terms_type` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24are_5fdistinct_5fterms_5ftype.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __are_distinct_terms_type x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __are_distinct_terms_type
  unfold EoCases.__are_distinct_terms_type.case_0 EoCases.__are_distinct_terms_type.case_1 EoCases.__are_distinct_terms_type.case_2 EoCases.__are_distinct_terms_type.case_3 EoCases.__are_distinct_terms_type.case_4 EoCases.__are_distinct_terms_type.case_5 EoCases.__are_distinct_terms_type.case_6 EoCases.__are_distinct_terms_type.case_7
  logos_eq

theorem body_eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24are_5fdistinct_5fterms_5ftype s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__are_distinct_terms_type x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24are_5fdistinct_5fterms_5ftype.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24are_5fdistinct_5fterms_5ftype
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  body_group_step with cases_0_0_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] = [] ++ [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2
  body_group_step with cases_0_1_eo__24are_5fdistinct_5fterms_5ftype_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] = [EoCases.__are_distinct_terms_type.case_0 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_1 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_2 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__are_distinct_terms_type.case_4 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_5 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_6 x_a0 x_a1 x_a2, EoCases.__are_distinct_terms_type.case_7 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 in EoCases.__are_distinct_terms_type.case_0 EoCases.__are_distinct_terms_type.case_1 EoCases.__are_distinct_terms_type.case_2 EoCases.__are_distinct_terms_type.case_3 EoCases.__are_distinct_terms_type.case_4 EoCases.__are_distinct_terms_type.case_5 EoCases.__are_distinct_terms_type.case_6 EoCases.__are_distinct_terms_type.case_7

theorem eo__24are_5fdistinct_5fterms_5ftype_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24are_5fdistinct_5fterms_5ftype.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24are_5fdistinct_5fterms_5ftype
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 5#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24are_5fdistinct_5fterms_5ftype s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__are_distinct_terms_type x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_5 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_5 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24are_5fdistinct_5fterms_5ftype_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5fmk_5fone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5fmk_5fone s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_mk_one.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_mk_one.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5fmk_5fone
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__arith_mk_one.case_0 using hn_a0

theorem case_1_eo__24arith_5fmk_5fone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5fmk_5fone s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_mk_one.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_mk_one.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5fmk_5fone
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_one.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  replace h_v2 := Represents.rep_of_eq h_v2 (y := Eo.Term.Rational (SmtEval.native_mk_rational (1) (1))) (by simp [SmtEval.native_mk_rational])
  case_done hinv2 hG with h_v2 in EoCases.__arith_mk_one.case_1 using hn_a0

/-- logos's `__arith_mk_one` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5fmk_5fone.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __arith_mk_one x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_mk_one.case_0 x_a0, EoCases.__arith_mk_one.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __arith_mk_one
  unfold EoCases.__arith_mk_one.case_0 EoCases.__arith_mk_one.case_1
  logos_eq

theorem body_eo__24arith_5fmk_5fone_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24arith_5fmk_5fone s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_mk_one x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5fmk_5fone.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24arith_5fmk_5fone
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24arith_5fmk_5fone_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24arith_5fmk_5fone_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__arith_mk_one.case_0 EoCases.__arith_mk_one.case_1

theorem eo__24arith_5fmk_5fone_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5fmk_5fone.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24arith_5fmk_5fone
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5fmk_5fone s1 a0) (fun s' t => Represents.rep s' t (__arith_mk_one x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5fmk_5fone_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5fmk_5fzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5fmk_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_mk_zero.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_mk_zero.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5fmk_5fzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_zero.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  case_done hinv2 hG with h_v1 in EoCases.__arith_mk_zero.case_0 using hn_a0

theorem case_1_eo__24arith_5fmk_5fzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5fmk_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_mk_zero.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_mk_zero.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5fmk_5fzero
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_zero.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying dropping h_a0 h_v0 hinv1 s1 v0
  replace h_v2 := Represents.rep_of_eq h_v2 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  case_done hinv2 hG with h_v2 in EoCases.__arith_mk_zero.case_1 using hn_a0

/-- logos's `__arith_mk_zero` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5fmk_5fzero.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __arith_mk_zero x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_mk_zero.case_0 x_a0, EoCases.__arith_mk_zero.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __arith_mk_zero
  unfold EoCases.__arith_mk_zero.case_0 EoCases.__arith_mk_zero.case_1
  logos_eq

theorem body_eo__24arith_5fmk_5fzero_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24arith_5fmk_5fzero s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_mk_zero x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5fmk_5fzero.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24arith_5fmk_5fzero
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24arith_5fmk_5fzero_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24arith_5fmk_5fzero_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__arith_mk_zero.case_0 EoCases.__arith_mk_zero.case_1

theorem eo__24arith_5fmk_5fzero_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5fmk_5fzero.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24arith_5fmk_5fzero
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5fmk_5fzero s1 a0) (fun s' t => Represents.rep s' t (__arith_mk_zero x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5fmk_5fzero_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_normalize_lit.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_normalize_lit.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v5 h_v6 dropping h_v1 h_v2 h_v3 he_v7 hinv1 e_v7 s1 v1 v2 v3
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  store_step with Store.apply_rep s2 v12 v13 _ _ hinv2 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_v10 dropping h_v12 h_v13 h_v5 h_v6 h_v7 h_v9 hinv2 s2 v12 v13 v5 v6 v7 v9
  store_step with Store.apply_rep s3 v14 v10 _ _ hinv3 h64 h_v14 h_v10 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying dropping h_v10 h_v14 hinv3 s3 v10 v14
  case_done hinv4 hG with h_v15 in EoCases.__arith_normalize_lit.case_0 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v9 hn_v10 hn_v12 hn_v13

theorem case_1_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_normalize_lit.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_normalize_lit.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  store_step with ih.eo__24arith_5frel_5fneg s1 v8 v9 v6 _ _ _ hinv1 h64 (hG.rem hrem) h_v8 h_v9 h_v6 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying dropping h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9 hinv1 s1 v1 v2 v3 v5 v6 v8 v9
  case_done hinv2 hG with h_v10 in EoCases.__arith_normalize_lit.case_1 using hn_a0 hn_v1 hn_v2 hn_v5 hn_v6 hn_v8 hn_v9

theorem case_2_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_normalize_lit.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_normalize_lit.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_normalize_lit.case_2
  store_step with Store.apply_rep s v4 v5 _ _ hinv h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 dropping h_a0 h_v1 h_v4 h_v5 v1 v4 v5
  store_step with Store.apply_rep s1 v6 v2 _ _ hinv1 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying dropping h_v2 h_v6 hinv1 s1 v2 v6
  case_done hinv2 hG with h_v7 in EoCases.__arith_normalize_lit.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__arith_normalize_lit` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5fnormalize_5flit.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __arith_normalize_lit x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_normalize_lit.case_0 x_a0, EoCases.__arith_normalize_lit.case_1 x_a0, EoCases.__arith_normalize_lit.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __arith_normalize_lit
  unfold EoCases.__arith_normalize_lit.case_0 EoCases.__arith_normalize_lit.case_1 EoCases.__arith_normalize_lit.case_2
  logos_eq

theorem body_eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24arith_5fnormalize_5flit s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_normalize_lit x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5fnormalize_5flit.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24arith_5fnormalize_5flit
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24arith_5fnormalize_5flit_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24arith_5fnormalize_5flit_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  case_step with case_2_eo__24arith_5fnormalize_5flit_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hn_a0 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hc0 hc1 hc2 in EoCases.__arith_normalize_lit.case_0 EoCases.__arith_normalize_lit.case_1 EoCases.__arith_normalize_lit.case_2

theorem eo__24arith_5fnormalize_5flit_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5fnormalize_5flit.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24arith_5fnormalize_5flit
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5fnormalize_5flit s1 a0) (fun s' t => Represents.rep s' t (__arith_normalize_lit x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5fnormalize_5flit_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_is_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_is_5fint.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  store_step with Store.apply_rep s4 v6 v2 _ _ hinv4 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with Store.apply_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v7 hinv5 s5 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v8 dropping he_v9 hinv6 e_v9 s6
  store_step with Store.apply_rep s7 v9 v2 _ _ hinv7 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v9 hinv7 s7 v9
  step as ⟨e_v11, he_v11⟩
  store_step with CtorSpec.eo_to_5freal.construct s8 e_v11 (by rw [he_v11]; exact empty_args) hinv8 h64 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v8 h_v10 dropping he_v11 hinv8 e_v11 s8
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo__40purify.construct s9 e_v12 (by rw [he_v12]; exact empty_args) hinv9 h64 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 h_v8 h_v10 h_v11 dropping he_v12 hinv9 e_v12 s9
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo_to_5fint.construct s10 e_v13 (by rw [he_v13]; exact empty_args) hinv10 h64 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v4 h_v8 h_v10 h_v11 h_v12 dropping he_v13 hinv10 e_v13 s10
  store_step with Store.apply_rep s11 v13 v2 _ _ hinv11 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v4 h_v8 h_v10 h_v11 h_v12 dropping h_v13 hinv11 s11 v13
  store_step with Store.apply_rep s12 v12 v14 _ _ hinv12 h64 h_v12 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v4 h_v8 h_v10 h_v11 dropping h_v12 h_v14 hinv12 s12 v12 v14
  store_step with Store.apply_rep s13 v11 v15 _ _ hinv13 h64 h_v11 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 h_v4 h_v8 h_v10 dropping h_v11 h_v15 hinv13 s13 v11 v15
  store_step with Store.apply_rep s14 v10 v16 _ _ hinv14 h64 h_v10 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v10 h_v16 hinv14 s14 v10 v16
  store_step with Store.apply_rep s15 v8 v17 _ _ hinv15 h64 h_v8 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v4 dropping h_v17 h_v8 hinv15 s15 v17 v8
  store_step with Store.apply_rep s16 v4 v18 _ _ hinv16 h64 h_v4 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 dropping h_v18 h_v4 hinv16 s16 v18 v4
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_and.construct s17 e_v20 (by rw [he_v20]; exact empty_args) hinv17 h64 as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v19 dropping he_v20 hinv17 e_v20 s17
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_and.construct s18 e_v21 (by rw [he_v21]; exact empty_args) hinv18 h64 as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v19 h_v20 dropping he_v21 hinv18 e_v21 s18
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__3c_3d.construct s19 e_v22 (by rw [he_v22]; exact empty_args) hinv19 h64 as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 dropping he_v22 hinv19 e_v22 s19
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s20 _ hinv20 h64 as ⟨v24, s21, hinv21, h_v24⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v22 dropping hinv20 s20
  replace h_v24 := Represents.rep_of_eq h_v24 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  store_step with Store.apply_rep s21 v22 v24 _ _ hinv21 h64 h_v22 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s22, hinv22, h_v25⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 dropping h_v22 h_v24 hinv21 s21 v22 v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__2d.construct s22 e_v26 (by rw [he_v26]; exact empty_args) hinv22 h64 as ⟨v26, s23, hinv23, h_v26⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 dropping he_v26 hinv22 e_v26 s22
  store_step with Store.apply_rep s23 v26 v2 _ _ hinv23 h64 h_v26 h_v2 (by ns_tac) (by ns_tac) as ⟨v27, s24, hinv24, h_v27⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 dropping h_v26 hinv23 s23 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_to_5freal.construct s24 e_v28 (by rw [he_v28]; exact empty_args) hinv24 h64 as ⟨v28, s25, hinv25, h_v28⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 h_v27 dropping he_v28 hinv24 e_v28 s24
  step as ⟨e_v29, he_v29⟩
  store_step with CtorSpec.eo__40purify.construct s25 e_v29 (by rw [he_v29]; exact empty_args) hinv25 h64 as ⟨v29, s26, hinv26, h_v29⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 h_v27 h_v28 dropping he_v29 hinv25 e_v29 s25
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_to_5fint.construct s26 e_v30 (by rw [he_v30]; exact empty_args) hinv26 h64 as ⟨v30, s27, hinv27, h_v30⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 h_v27 h_v28 h_v29 dropping he_v30 hinv26 e_v30 s26
  store_step with Store.apply_rep s27 v30 v2 _ _ hinv27 h64 h_v30 h_v2 (by ns_tac) (by ns_tac) as ⟨v31, s28, hinv28, h_v31⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 h_v27 h_v28 h_v29 dropping h_v30 hinv27 s27 v30
  store_step with Store.apply_rep s28 v29 v31 _ _ hinv28 h64 h_v29 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s29, hinv29, h_v32⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 h_v27 h_v28 dropping h_v29 h_v31 hinv28 s28 v29 v31
  store_step with Store.apply_rep s29 v28 v32 _ _ hinv29 h64 h_v28 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s30, hinv30, h_v33⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 h_v27 dropping h_v28 h_v32 hinv29 s29 v28 v32
  store_step with Store.apply_rep s30 v27 v33 _ _ hinv30 h64 h_v27 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s31, hinv31, h_v34⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 h_v25 dropping h_v27 h_v33 hinv30 s30 v27 v33
  store_step with Store.apply_rep s31 v25 v34 _ _ hinv31 h64 h_v25 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s32, hinv32, h_v35⟩ growing hG carrying h_v2 h_v19 h_v20 h_v21 dropping h_v25 h_v34 hinv31 s31 v25 v34
  store_step with Store.apply_rep s32 v21 v35 _ _ hinv32 h64 h_v21 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s33, hinv33, h_v36⟩ growing hG carrying h_v2 h_v19 h_v20 dropping h_v21 h_v35 hinv32 s32 v21 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_and.construct s33 e_v37 (by rw [he_v37]; exact empty_args) hinv33 h64 as ⟨v37, s34, hinv34, h_v37⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 dropping he_v37 hinv33 e_v37 s33
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__3c.construct s34 e_v38 (by rw [he_v38]; exact empty_args) hinv34 h64 as ⟨v38, s35, hinv35, h_v38⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 h_v37 dropping he_v38 hinv34 e_v38 s34
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__2d.construct s35 e_v39 (by rw [he_v39]; exact empty_args) hinv35 h64 as ⟨v39, s36, hinv36, h_v39⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 h_v37 h_v38 dropping he_v39 hinv35 e_v39 s35
  store_step with Store.apply_rep s36 v39 v2 _ _ hinv36 h64 h_v39 h_v2 (by ns_tac) (by ns_tac) as ⟨v40, s37, hinv37, h_v40⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 h_v37 h_v38 dropping h_v39 hinv36 s36 v39
  step as ⟨e_v41, he_v41⟩
  store_step with CtorSpec.eo_to_5freal.construct s37 e_v41 (by rw [he_v41]; exact empty_args) hinv37 h64 as ⟨v41, s38, hinv38, h_v41⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 h_v37 h_v38 h_v40 dropping he_v41 hinv37 e_v41 s37
  step as ⟨e_v42, he_v42⟩
  store_step with CtorSpec.eo__40purify.construct s38 e_v42 (by rw [he_v42]; exact empty_args) hinv38 h64 as ⟨v42, s39, hinv39, h_v42⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 h_v37 h_v38 h_v40 h_v41 dropping he_v42 hinv38 e_v42 s38
  step as ⟨e_v43, he_v43⟩
  store_step with CtorSpec.eo_to_5fint.construct s39 e_v43 (by rw [he_v43]; exact empty_args) hinv39 h64 as ⟨v43, s40, hinv40, h_v43⟩ growing hG carrying h_v2 h_v19 h_v20 h_v36 h_v37 h_v38 h_v40 h_v41 h_v42 dropping he_v43 hinv39 e_v43 s39
  store_step with Store.apply_rep s40 v43 v2 _ _ hinv40 h64 h_v43 h_v2 (by ns_tac) (by ns_tac) as ⟨v44, s41, hinv41, h_v44⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 h_v38 h_v40 h_v41 h_v42 dropping h_v2 h_v43 hinv40 s40 v2 v43
  store_step with Store.apply_rep s41 v42 v44 _ _ hinv41 h64 h_v42 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s42, hinv42, h_v45⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 h_v38 h_v40 h_v41 dropping h_v42 h_v44 hinv41 s41 v42 v44
  store_step with Store.apply_rep s42 v41 v45 _ _ hinv42 h64 h_v41 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s43, hinv43, h_v46⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 h_v38 h_v40 dropping h_v41 h_v45 hinv42 s42 v41 v45
  store_step with Store.apply_rep s43 v40 v46 _ _ hinv43 h64 h_v40 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s44, hinv44, h_v47⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 h_v38 dropping h_v40 h_v46 hinv43 s43 v40 v46
  store_step with Store.apply_rep s44 v38 v47 _ _ hinv44 h64 h_v38 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s45, hinv45, h_v48⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 dropping h_v38 h_v47 hinv44 s44 v38 v47
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s45 _ hinv45 h64 as ⟨v50, s46, hinv46, h_v50⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 h_v48 dropping hinv45 s45
  replace h_v50 := Represents.rep_of_eq h_v50 (y := Eo.Term.Rational (SmtEval.native_mk_rational (1) (1))) (by simp [SmtEval.native_mk_rational])
  store_step with Store.apply_rep s46 v48 v50 _ _ hinv46 h64 h_v48 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s47, hinv47, h_v51⟩ growing hG carrying h_v19 h_v20 h_v36 h_v37 dropping h_v48 h_v50 hinv46 s46 v48 v50
  store_step with Store.apply_rep s47 v37 v51 _ _ hinv47 h64 h_v37 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s48, hinv48, h_v52⟩ growing hG carrying h_v19 h_v20 h_v36 dropping h_v37 h_v51 hinv47 s47 v37 v51
  store_step with Store.literal_boolean_spec s48 true hinv48 h64 as ⟨v53, s49, hinv49, h_v53⟩ growing hG carrying h_v19 h_v20 h_v36 h_v52 dropping hinv48 s48
  store_step with Store.apply_rep s49 v52 v53 _ _ hinv49 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s50, hinv50, h_v54⟩ growing hG carrying h_v19 h_v20 h_v36 dropping h_v52 h_v53 hinv49 s49 v52 v53
  store_step with Store.apply_rep s50 v36 v54 _ _ hinv50 h64 h_v36 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s51, hinv51, h_v55⟩ growing hG carrying h_v19 h_v20 dropping h_v36 h_v54 hinv50 s50 v36 v54
  store_step with Store.apply_rep s51 v20 v55 _ _ hinv51 h64 h_v20 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s52, hinv52, h_v56⟩ growing hG carrying h_v19 dropping h_v20 h_v55 hinv51 s51 v20 v55
  store_step with Store.literal_boolean_spec s52 true hinv52 h64 as ⟨v57, s53, hinv53, h_v57⟩ growing hG carrying h_v19 h_v56 dropping hinv52 s52
  store_step with Store.apply_rep s53 v56 v57 _ _ hinv53 h64 h_v56 h_v57 (by ns_tac) (by ns_tac) as ⟨v58, s54, hinv54, h_v58⟩ growing hG carrying h_v19 dropping h_v56 h_v57 hinv53 s53 v56 v57
  store_step with Store.apply_rep s54 v19 v58 _ _ hinv54 h64 h_v19 h_v58 (by ns_tac) (by ns_tac) as ⟨v59, s55, hinv55, h_v59⟩ growing hG carrying dropping h_v19 h_v58 hinv54 s54 v19 v58
  case_done hinv55 hG with h_v59 in EoCases.__arith_reduction_pred.case_0 using hn_a0 hn_v1 hn_v2

theorem case_1_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_to_5fint.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_1
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_to_5fint.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  store_step with Store.apply_rep s4 v6 v2 _ _ hinv4 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with Store.apply_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v7 hinv5 s5 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40purify.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v8 dropping he_v9 hinv6 e_v9 s6
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_to_5fint.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping he_v10 hinv7 e_v10 s7
  store_step with Store.apply_rep s8 v10 v2 _ _ hinv8 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping h_v10 hinv8 s8 v10
  store_step with Store.apply_rep s9 v9 v11 _ _ hinv9 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v11 h_v9 hinv9 s9 v11 v9
  store_step with Store.apply_rep s10 v8 v12 _ _ hinv10 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v4 dropping h_v12 h_v8 hinv10 s10 v12 v8
  store_step with Store.apply_rep s11 v4 v13 _ _ hinv11 h64 h_v4 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 dropping h_v13 h_v4 hinv11 s11 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_and.construct s12 e_v15 (by rw [he_v15]; exact empty_args) hinv12 h64 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v14 dropping he_v15 hinv12 e_v15 s12
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_and.construct s13 e_v16 (by rw [he_v16]; exact empty_args) hinv13 h64 as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 h_v14 h_v15 dropping he_v16 hinv13 e_v16 s13
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3c_3d.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 dropping he_v17 hinv14 e_v17 s14
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s15 _ hinv15 h64 as ⟨v19, s16, hinv16, h_v19⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v17 dropping hinv15 s15
  replace h_v19 := Represents.rep_of_eq h_v19 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  store_step with Store.apply_rep s16 v17 v19 _ _ hinv16 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s17, hinv17, h_v20⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 dropping h_v17 h_v19 hinv16 s16 v17 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__2d.construct s17 e_v21 (by rw [he_v21]; exact empty_args) hinv17 h64 as ⟨v21, s18, hinv18, h_v21⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 dropping he_v21 hinv17 e_v21 s17
  store_step with Store.apply_rep s18 v21 v2 _ _ hinv18 h64 h_v21 h_v2 (by ns_tac) (by ns_tac) as ⟨v22, s19, hinv19, h_v22⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 dropping h_v21 hinv18 s18 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_to_5freal.construct s19 e_v23 (by rw [he_v23]; exact empty_args) hinv19 h64 as ⟨v23, s20, hinv20, h_v23⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 h_v22 dropping he_v23 hinv19 e_v23 s19
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__40purify.construct s20 e_v24 (by rw [he_v24]; exact empty_args) hinv20 h64 as ⟨v24, s21, hinv21, h_v24⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 h_v22 h_v23 dropping he_v24 hinv20 e_v24 s20
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_to_5fint.construct s21 e_v25 (by rw [he_v25]; exact empty_args) hinv21 h64 as ⟨v25, s22, hinv22, h_v25⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 h_v22 h_v23 h_v24 dropping he_v25 hinv21 e_v25 s21
  store_step with Store.apply_rep s22 v25 v2 _ _ hinv22 h64 h_v25 h_v2 (by ns_tac) (by ns_tac) as ⟨v26, s23, hinv23, h_v26⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 h_v22 h_v23 h_v24 dropping h_v25 hinv22 s22 v25
  store_step with Store.apply_rep s23 v24 v26 _ _ hinv23 h64 h_v24 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s24, hinv24, h_v27⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 h_v22 h_v23 dropping h_v24 h_v26 hinv23 s23 v24 v26
  store_step with Store.apply_rep s24 v23 v27 _ _ hinv24 h64 h_v23 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s25, hinv25, h_v28⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 h_v22 dropping h_v23 h_v27 hinv24 s24 v23 v27
  store_step with Store.apply_rep s25 v22 v28 _ _ hinv25 h64 h_v22 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s26, hinv26, h_v29⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v20 dropping h_v22 h_v28 hinv25 s25 v22 v28
  store_step with Store.apply_rep s26 v20 v29 _ _ hinv26 h64 h_v20 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s27, hinv27, h_v30⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 dropping h_v20 h_v29 hinv26 s26 v20 v29
  store_step with Store.apply_rep s27 v16 v30 _ _ hinv27 h64 h_v16 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s28, hinv28, h_v31⟩ growing hG carrying h_v2 h_v14 h_v15 dropping h_v16 h_v30 hinv27 s27 v16 v30
  step as ⟨e_v32, he_v32⟩
  store_step with CtorSpec.eo_and.construct s28 e_v32 (by rw [he_v32]; exact empty_args) hinv28 h64 as ⟨v32, s29, hinv29, h_v32⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 dropping he_v32 hinv28 e_v32 s28
  step as ⟨e_v33, he_v33⟩
  store_step with CtorSpec.eo__3c.construct s29 e_v33 (by rw [he_v33]; exact empty_args) hinv29 h64 as ⟨v33, s30, hinv30, h_v33⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 h_v32 dropping he_v33 hinv29 e_v33 s29
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo__2d.construct s30 e_v34 (by rw [he_v34]; exact empty_args) hinv30 h64 as ⟨v34, s31, hinv31, h_v34⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 h_v32 h_v33 dropping he_v34 hinv30 e_v34 s30
  store_step with Store.apply_rep s31 v34 v2 _ _ hinv31 h64 h_v34 h_v2 (by ns_tac) (by ns_tac) as ⟨v35, s32, hinv32, h_v35⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 h_v32 h_v33 dropping h_v34 hinv31 s31 v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo_to_5freal.construct s32 e_v36 (by rw [he_v36]; exact empty_args) hinv32 h64 as ⟨v36, s33, hinv33, h_v36⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 h_v32 h_v33 h_v35 dropping he_v36 hinv32 e_v36 s32
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__40purify.construct s33 e_v37 (by rw [he_v37]; exact empty_args) hinv33 h64 as ⟨v37, s34, hinv34, h_v37⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 h_v32 h_v33 h_v35 h_v36 dropping he_v37 hinv33 e_v37 s33
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo_to_5fint.construct s34 e_v38 (by rw [he_v38]; exact empty_args) hinv34 h64 as ⟨v38, s35, hinv35, h_v38⟩ growing hG carrying h_v2 h_v14 h_v15 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 dropping he_v38 hinv34 e_v38 s34
  store_step with Store.apply_rep s35 v38 v2 _ _ hinv35 h64 h_v38 h_v2 (by ns_tac) (by ns_tac) as ⟨v39, s36, hinv36, h_v39⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 h_v33 h_v35 h_v36 h_v37 dropping h_v2 h_v38 hinv35 s35 v2 v38
  store_step with Store.apply_rep s36 v37 v39 _ _ hinv36 h64 h_v37 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s37, hinv37, h_v40⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 h_v33 h_v35 h_v36 dropping h_v37 h_v39 hinv36 s36 v37 v39
  store_step with Store.apply_rep s37 v36 v40 _ _ hinv37 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s38, hinv38, h_v41⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 h_v33 h_v35 dropping h_v36 h_v40 hinv37 s37 v36 v40
  store_step with Store.apply_rep s38 v35 v41 _ _ hinv38 h64 h_v35 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s39, hinv39, h_v42⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 h_v33 dropping h_v35 h_v41 hinv38 s38 v35 v41
  store_step with Store.apply_rep s39 v33 v42 _ _ hinv39 h64 h_v33 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s40, hinv40, h_v43⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 dropping h_v33 h_v42 hinv39 s39 v33 v42
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s40 _ hinv40 h64 as ⟨v45, s41, hinv41, h_v45⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 h_v43 dropping hinv40 s40
  replace h_v45 := Represents.rep_of_eq h_v45 (y := Eo.Term.Rational (SmtEval.native_mk_rational (1) (1))) (by simp [SmtEval.native_mk_rational])
  store_step with Store.apply_rep s41 v43 v45 _ _ hinv41 h64 h_v43 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s42, hinv42, h_v46⟩ growing hG carrying h_v14 h_v15 h_v31 h_v32 dropping h_v43 h_v45 hinv41 s41 v43 v45
  store_step with Store.apply_rep s42 v32 v46 _ _ hinv42 h64 h_v32 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s43, hinv43, h_v47⟩ growing hG carrying h_v14 h_v15 h_v31 dropping h_v32 h_v46 hinv42 s42 v32 v46
  store_step with Store.literal_boolean_spec s43 true hinv43 h64 as ⟨v48, s44, hinv44, h_v48⟩ growing hG carrying h_v14 h_v15 h_v31 h_v47 dropping hinv43 s43
  store_step with Store.apply_rep s44 v47 v48 _ _ hinv44 h64 h_v47 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s45, hinv45, h_v49⟩ growing hG carrying h_v14 h_v15 h_v31 dropping h_v47 h_v48 hinv44 s44 v47 v48
  store_step with Store.apply_rep s45 v31 v49 _ _ hinv45 h64 h_v31 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s46, hinv46, h_v50⟩ growing hG carrying h_v14 h_v15 dropping h_v31 h_v49 hinv45 s45 v31 v49
  store_step with Store.apply_rep s46 v15 v50 _ _ hinv46 h64 h_v15 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s47, hinv47, h_v51⟩ growing hG carrying h_v14 dropping h_v15 h_v50 hinv46 s46 v15 v50
  store_step with Store.literal_boolean_spec s47 true hinv47 h64 as ⟨v52, s48, hinv48, h_v52⟩ growing hG carrying h_v14 h_v51 dropping hinv47 s47
  store_step with Store.apply_rep s48 v51 v52 _ _ hinv48 h64 h_v51 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s49, hinv49, h_v53⟩ growing hG carrying h_v14 dropping h_v51 h_v52 hinv48 s48 v51 v52
  store_step with Store.apply_rep s49 v14 v53 _ _ hinv49 h64 h_v14 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s50, hinv50, h_v54⟩ growing hG carrying dropping h_v14 h_v53 hinv49 s49 v14 v53
  case_done hinv50 hG with h_v54 in EoCases.__arith_reduction_pred.case_1 using hn_a0 hn_v1 hn_v2

theorem case_2_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2f.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__2f.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v2 _ _ hinv8 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v13 hinv8 s8 v13
  store_step with ih.eo__24eo_5ftypeof s9 v2 _ hinv9 h64 (hG.rem hrem) h_v2 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 h_v14 dropping hinv9 s9
  store_step with ih.eo__24arith_5fmk_5fzero s10 v15 _ hinv10 h64 (hG.rem hrem) h_v15 as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 h_v14 dropping h_v15 hinv10 s10 v15
  store_step with Store.apply_mk_rep s11 v14 v16 _ _ hinv11 h64 h_v14 h_v16 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v14 h_v16 hinv11 s11 v14 v16
  store_step with Store.apply_mk_rep s12 v12 v17 _ _ hinv12 h64 h_v12 h_v17 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v12 h_v17 hinv12 s12 v12 v17
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo__40div_5fby_5fzero.construct s13 e_v19 (by rw [he_v19]; exact empty_args) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 dropping he_v19 hinv13 e_v19 s13
  store_step with ih.eo__24eo_5ftypeof s14 v5 _ hinv14 h64 (hG.rem hrem) h_v5 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 h_v19 dropping hinv14 s14
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_Int.construct s15 e_v21 (by rw [he_v21]; exact empty_args) hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 h_v19 h_v20 dropping he_v21 hinv15 e_v21 s15
  step as ⟨e_v22, he_v22⟩
  store_step with Store.builtin_spec_eq s16 e_v22 (by rw [he_v22]; rfl) h_v20 h_v21 hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 h_v19 dropping h_v20 h_v21 he_v22 hinv16 e_v22 s16 v20 v21
  have h_ite_v25 := (show if_8_eo__24arith_5freduction_5fpred s17 v22 v5 ⦃ r s' => s'.Inv ∧ s17.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_8_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s17
    rcases Store.boolean_value_term h_v22 with ⟨hx_23, hbv_23⟩ | ⟨hx_23, hbv_23⟩ | ⟨hx_23, hbv_23⟩
    · ite_branch hbv_23
      step as ⟨e_v23, he_v23⟩
      store_step with CtorSpec.eo_to_5freal.construct s17 e_v23 (by rw [he_v23]; exact empty_args) hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 h_v19 dropping h_v22 he_v23 e_v23 v22
      store_step with Store.apply_rep s18 v23 v5 _ _ hinv18 h64 h_v23 h_v5 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 h_v19 dropping h_v23 v23
      ite_done hinv19 hG with (eo_ite_true_rep _ hx_23 h_v24)
    · ite_branch hbv_23
      ite_done hinv17 hG with (eo_ite_false_rep _ hx_23 h_v5)
    · ite_branch hbv_23
      ite_stuck hinv17 hG with hx_23)
  store_step with h_ite_v25 as ⟨v25, s18, hinv18, h_v25⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 h_v19 dropping h_ite_v25 h_v22 hinv17 s17 v22
  store_step with Store.apply_mk_rep s18 v19 v25 _ _ hinv18 h64 h_v19 h_v25 as ⟨v26, s19, hinv19, h_v26⟩ growing hG carrying h_v2 h_v5 h_v11 h_v18 dropping h_v19 h_v25 hinv18 s18 v19 v25
  store_step with Store.apply_mk_rep s19 v18 v26 _ _ hinv19 h64 h_v18 h_v26 as ⟨v27, s20, hinv20, h_v27⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v18 h_v26 hinv19 s19 v18 v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s20 e_v28 (by rw [he_v28]; exact empty_args) hinv20 h64 as ⟨v28, s21, hinv21, h_v28⟩ growing hG carrying h_v2 h_v5 h_v11 h_v27 dropping he_v28 hinv20 e_v28 s20
  store_step with Store.apply_rep s21 v28 v5 _ _ hinv21 h64 h_v28 h_v5 (by ns_tac) (by ns_tac) as ⟨v29, s22, hinv22, h_v29⟩ growing hG carrying h_v2 h_v11 h_v27 dropping h_v28 h_v5 hinv21 s21 v28 v5
  store_step with Store.apply_rep s22 v29 v2 _ _ hinv22 h64 h_v29 h_v2 (by ns_tac) (by ns_tac) as ⟨v30, s23, hinv23, h_v30⟩ growing hG carrying h_v11 h_v27 dropping h_v2 h_v29 hinv22 s22 v2 v29
  store_step with Store.apply_mk_rep s23 v27 v30 _ _ hinv23 h64 h_v27 h_v30 as ⟨v31, s24, hinv24, h_v31⟩ growing hG carrying h_v11 dropping h_v27 h_v30 hinv23 s23 v27 v30
  store_step with Store.apply_mk_rep s24 v11 v31 _ _ hinv24 h64 h_v11 h_v31 as ⟨v32, s25, hinv25, h_v32⟩ growing hG carrying dropping h_v11 h_v31 hinv24 s24 v11 v31
  case_done hinv25 hG with h_v32 in EoCases.__arith_reduction_pred.case_2 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_3_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_3 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_3
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_3
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_div.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_3
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_div.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v2 _ _ hinv8 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v13 hinv8 s8 v13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 h_v14 dropping hinv9 s9
  store_step with Store.apply_rep s10 v14 v15 _ _ hinv10 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v14 h_v15 hinv10 s10 v14 v15
  store_step with Store.apply_rep s11 v12 v16 _ _ hinv11 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v12 h_v16 hinv11 s11 v12 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__40int_5fdiv_5fby_5fzero.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v11 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 v5 _ _ hinv13 h64 h_v18 h_v5 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v11 h_v17 dropping h_v18 hinv13 s13 v18
  store_step with Store.apply_rep s14 v17 v19 _ _ hinv14 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v17 h_v19 hinv14 s14 v17 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s15 e_v21 (by rw [he_v21]; exact empty_args) hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v11 h_v20 dropping he_v21 hinv15 e_v21 s15
  store_step with Store.apply_rep s16 v21 v5 _ _ hinv16 h64 h_v21 h_v5 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v11 h_v20 dropping h_v21 h_v5 hinv16 s16 v21 v5
  store_step with Store.apply_rep s17 v22 v2 _ _ hinv17 h64 h_v22 h_v2 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v11 h_v20 dropping h_v2 h_v22 hinv17 s17 v2 v22
  store_step with Store.apply_rep s18 v20 v23 _ _ hinv18 h64 h_v20 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v11 dropping h_v20 h_v23 hinv18 s18 v20 v23
  store_step with Store.apply_rep s19 v11 v24 _ _ hinv19 h64 h_v11 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying dropping h_v11 h_v24 hinv19 s19 v11 v24
  case_done hinv20 hG with h_v25 in EoCases.__arith_reduction_pred.case_3 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_4_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_4 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_4 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_4
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_4
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_4
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_mod.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  store_step with Store.apply_rep s3 v8 v5 _ _ hinv3 h64 h_v8 h_v5 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v8 hinv3 s3 v8
  store_step with Store.apply_rep s4 v9 v2 _ _ hinv4 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v7 v10 _ _ hinv5 h64 h_v7 h_v10 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 dropping h_v10 h_v7 hinv5 s5 v10 v7
  step as ⟨e_v12, he_v12⟩
  store_step with CtorSpec.eo_ite.construct s6 e_v12 (by rw [he_v12]; exact empty_args) hinv6 h64 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v11 dropping he_v12 hinv6 e_v12 s6
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__3d.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v2 _ _ hinv8 h64 h_v13 h_v2 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v13 hinv8 s8 v13
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s9 0#u32 (0) (by scalar_tac) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 h_v14 dropping hinv9 s9
  store_step with Store.apply_rep s10 v14 v15 _ _ hinv10 h64 h_v14 h_v15 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v11 h_v12 dropping h_v14 h_v15 hinv10 s10 v14 v15
  store_step with Store.apply_rep s11 v12 v16 _ _ hinv11 h64 h_v12 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v12 h_v16 hinv11 s11 v12 v16
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__40mod_5fby_5fzero.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v11 h_v17 dropping he_v18 hinv12 e_v18 s12
  store_step with Store.apply_rep s13 v18 v5 _ _ hinv13 h64 h_v18 h_v5 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v11 h_v17 dropping h_v18 hinv13 s13 v18
  store_step with Store.apply_rep s14 v17 v19 _ _ hinv14 h64 h_v17 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v11 dropping h_v17 h_v19 hinv14 s14 v17 v19
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s15 e_v21 (by rw [he_v21]; exact empty_args) hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v11 h_v20 dropping he_v21 hinv15 e_v21 s15
  store_step with Store.apply_rep s16 v21 v5 _ _ hinv16 h64 h_v21 h_v5 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v11 h_v20 dropping h_v21 h_v5 hinv16 s16 v21 v5
  store_step with Store.apply_rep s17 v22 v2 _ _ hinv17 h64 h_v22 h_v2 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v11 h_v20 dropping h_v2 h_v22 hinv17 s17 v2 v22
  store_step with Store.apply_rep s18 v20 v23 _ _ hinv18 h64 h_v20 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v11 dropping h_v20 h_v23 hinv18 s18 v20 v23
  store_step with Store.apply_rep s19 v11 v24 _ _ hinv19 h64 h_v11 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying dropping h_v11 h_v24 hinv19 s19 v11 v24
  case_done hinv20 hG with h_v25 in EoCases.__arith_reduction_pred.case_4 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 2070000 in
theorem case_5_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_5_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_5 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_5 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_5
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_5
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40purify.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping he_v13 hinv7 e_v13 s7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v13 dropping he_v14 hinv8 e_v14 s8
  store_step with Store.apply_rep s9 v14 v5 _ _ hinv9 h64 h_v14 h_v5 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v13 dropping h_v14 hinv9 s9 v14
  store_step with Store.apply_rep s10 v15 v2 _ _ hinv10 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v13 dropping h_v15 hinv10 s10 v15
  store_step with Store.apply_rep s11 v13 v16 _ _ hinv11 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping h_v13 h_v16 hinv11 s11 v13 v16
  store_step with Store.apply_rep s12 v12 v17 _ _ hinv12 h64 h_v12 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v12 h_v17 hinv12 s12 v12 v17
  store_step with Store.apply_rep s13 v7 v18 _ _ hinv13 h64 h_v7 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 dropping h_v18 h_v7 hinv13 s13 v18 v7
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_and.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v19 dropping he_v20 hinv14 e_v20 s14
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__3d_3e.construct s15 e_v21 (by rw [he_v21]; exact empty_args) hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping he_v21 hinv15 e_v21 s15
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo_not.construct s16 e_v22 (by rw [he_v22]; exact empty_args) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 dropping he_v22 hinv16 e_v22 s16
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo__3d.construct s17 e_v23 (by rw [he_v23]; exact empty_args) hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 dropping he_v23 hinv17 e_v23 s17
  store_step with ih.eo__24eo_5ftypeof s18 v2 _ hinv18 h64 (hG.rem hrem) h_v2 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v23 dropping hinv18 s18
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_Int.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 dropping he_v25 hinv19 e_v25 s19
  step as ⟨e_v26, he_v26⟩
  store_step with Store.builtin_spec_eq s20 e_v26 (by rw [he_v26]; rfl) h_v24 h_v25 hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v23 dropping h_v24 h_v25 he_v26 hinv20 e_v26 s20 v24 v25
  have h_ite_v29 := (show if_13_eo__24arith_5freduction_5fpred s21 v26 v2 ⦃ r s' => s'.Inv ∧ s21.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_13_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s21
    rcases Store.boolean_value_term h_v26 with ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩ | ⟨hx_27, hbv_27⟩
    · ite_branch hbv_27
      step as ⟨e_v27, he_v27⟩
      store_step with CtorSpec.eo_to_5freal.construct s21 e_v27 (by rw [he_v27]; exact empty_args) hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v23 dropping h_v26 he_v27 e_v27 v26
      store_step with Store.apply_rep s22 v27 v2 _ _ hinv22 h64 h_v27 h_v2 (by ns_tac) (by ns_tac) as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v23 dropping h_v27 v27
      ite_done hinv23 hG with (eo_ite_true_rep _ hx_27 h_v28)
    · ite_branch hbv_27
      ite_done hinv21 hG with (eo_ite_false_rep _ hx_27 h_v2)
    · ite_branch hbv_27
      ite_stuck hinv21 hG with hx_27)
  store_step with h_ite_v29 as ⟨v29, s22, hinv22, h_v29⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v23 dropping h_ite_v29 h_v26 hinv21 s21 v26
  store_step with Store.apply_mk_rep s22 v23 v29 _ _ hinv22 h64 h_v23 h_v29 as ⟨v30, s23, hinv23, h_v30⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 dropping h_v23 h_v29 hinv22 s22 v23 v29
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s23 _ hinv23 h64 as ⟨v32, s24, hinv24, h_v32⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 h_v30 dropping hinv23 s23
  replace h_v32 := Represents.rep_of_eq h_v32 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  store_step with Store.apply_mk_rep s24 v30 v32 _ _ hinv24 h64 h_v30 h_v32 as ⟨v33, s25, hinv25, h_v33⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 h_v22 dropping h_v30 h_v32 hinv24 s24 v30 v32
  store_step with Store.apply_mk_rep s25 v22 v33 _ _ hinv25 h64 h_v22 h_v33 as ⟨v34, s26, hinv26, h_v34⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v21 dropping h_v22 h_v33 hinv25 s25 v22 v33
  store_step with Store.apply_mk_rep s26 v21 v34 _ _ hinv26 h64 h_v21 h_v34 as ⟨v35, s27, hinv27, h_v35⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v21 h_v34 hinv26 s26 v21 v34
  step as ⟨e_v36, he_v36⟩
  store_step with CtorSpec.eo__3d.construct s27 e_v36 (by rw [he_v36]; exact empty_args) hinv27 h64 as ⟨v36, s28, hinv28, h_v36⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 dropping he_v36 hinv27 e_v36 s27
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo__2a.construct s28 e_v37 (by rw [he_v37]; exact empty_args) hinv28 h64 as ⟨v37, s29, hinv29, h_v37⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 dropping he_v37 hinv28 e_v37 s28
  store_step with ih.eo__24eo_5ftypeof s29 v2 _ hinv29 h64 (hG.rem hrem) h_v2 as ⟨v38, s30, hinv30, h_v38⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v37 dropping hinv29 s29
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo_Int.construct s30 e_v39 (by rw [he_v39]; exact empty_args) hinv30 h64 as ⟨v39, s31, hinv31, h_v39⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v37 h_v38 dropping he_v39 hinv30 e_v39 s30
  step as ⟨e_v40, he_v40⟩
  store_step with Store.builtin_spec_eq s31 e_v40 (by rw [he_v40]; rfl) h_v38 h_v39 hinv31 h64 as ⟨v40, s32, hinv32, h_v40⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v37 dropping h_v38 h_v39 he_v40 hinv31 e_v40 s31 v38 v39
  have h_ite_v43 := (show if_14_eo__24arith_5freduction_5fpred s32 v40 v2 ⦃ r s' => s'.Inv ∧ s32.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_14_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s32
    rcases Store.boolean_value_term h_v40 with ⟨hx_41, hbv_41⟩ | ⟨hx_41, hbv_41⟩ | ⟨hx_41, hbv_41⟩
    · ite_branch hbv_41
      step as ⟨e_v41, he_v41⟩
      store_step with CtorSpec.eo_to_5freal.construct s32 e_v41 (by rw [he_v41]; exact empty_args) hinv32 h64 as ⟨v41, s33, hinv33, h_v41⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v37 dropping h_v40 he_v41 e_v41 v40
      store_step with Store.apply_rep s33 v41 v2 _ _ hinv33 h64 h_v41 h_v2 (by ns_tac) (by ns_tac) as ⟨v42, s34, hinv34, h_v42⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v37 dropping h_v41 v41
      ite_done hinv34 hG with (eo_ite_true_rep _ hx_41 h_v42)
    · ite_branch hbv_41
      ite_done hinv32 hG with (eo_ite_false_rep _ hx_41 h_v2)
    · ite_branch hbv_41
      ite_stuck hinv32 hG with hx_41)
  store_step with h_ite_v43 as ⟨v43, s33, hinv33, h_v43⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v37 dropping h_ite_v43 h_v40 hinv32 s32 v40
  store_step with Store.apply_mk_rep s33 v37 v43 _ _ hinv33 h64 h_v37 h_v43 as ⟨v44, s34, hinv34, h_v44⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 dropping h_v37 h_v43 hinv33 s33 v37 v43
  step as ⟨e_v45, he_v45⟩
  store_step with CtorSpec.eo__2a.construct s34 e_v45 (by rw [he_v45]; exact empty_args) hinv34 h64 as ⟨v45, s35, hinv35, h_v45⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 dropping he_v45 hinv34 e_v45 s34
  step as ⟨e_v46, he_v46⟩
  store_step with CtorSpec.eo__40purify.construct s35 e_v46 (by rw [he_v46]; exact empty_args) hinv35 h64 as ⟨v46, s36, hinv36, h_v46⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v45 dropping he_v46 hinv35 e_v46 s35
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__2f_5ftotal.construct s36 e_v47 (by rw [he_v47]; exact empty_args) hinv36 h64 as ⟨v47, s37, hinv37, h_v47⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v45 h_v46 dropping he_v47 hinv36 e_v47 s36
  store_step with Store.apply_rep s37 v47 v5 _ _ hinv37 h64 h_v47 h_v5 (by ns_tac) (by ns_tac) as ⟨v48, s38, hinv38, h_v48⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v45 h_v46 dropping h_v47 hinv37 s37 v47
  store_step with Store.apply_rep s38 v48 v2 _ _ hinv38 h64 h_v48 h_v2 (by ns_tac) (by ns_tac) as ⟨v49, s39, hinv39, h_v49⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v45 h_v46 dropping h_v48 hinv38 s38 v48
  store_step with Store.apply_rep s39 v46 v49 _ _ hinv39 h64 h_v46 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s40, hinv40, h_v50⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v45 dropping h_v46 h_v49 hinv39 s39 v46 v49
  store_step with Store.apply_rep s40 v45 v50 _ _ hinv40 h64 h_v45 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s41, hinv41, h_v51⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 dropping h_v45 h_v50 hinv40 s40 v45 v50
  step as ⟨e_v52, he_v52⟩
  store_step with CtorSpec.eo__2a.construct s41 e_v52 (by rw [he_v52]; exact empty_args) hinv41 h64 as ⟨v52, s42, hinv42, h_v52⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 dropping he_v52 hinv41 e_v52 s41
  store_step with ih.eo__24eo_5ftypeof s42 v2 _ hinv42 h64 (hG.rem hrem) h_v2 as ⟨v53, s43, hinv43, h_v53⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 dropping hinv42 s42
  step as ⟨e_v54, he_v54⟩
  store_step with CtorSpec.eo_Int.construct s43 e_v54 (by rw [he_v54]; exact empty_args) hinv43 h64 as ⟨v54, s44, hinv44, h_v54⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 h_v53 dropping he_v54 hinv43 e_v54 s43
  step as ⟨e_v55, he_v55⟩
  store_step with Store.builtin_spec_eq s44 e_v55 (by rw [he_v55]; rfl) h_v53 h_v54 hinv44 h64 as ⟨v55, s45, hinv45, h_v55⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 dropping h_v53 h_v54 he_v55 hinv44 e_v55 s44 v53 v54
  have h_ite_v58 := (show if_15_eo__24arith_5freduction_5fpred s45 v55 v2 ⦃ r s' => s'.Inv ∧ s45.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_15_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s45
    rcases Store.boolean_value_term h_v55 with ⟨hx_56, hbv_56⟩ | ⟨hx_56, hbv_56⟩ | ⟨hx_56, hbv_56⟩
    · ite_branch hbv_56
      step as ⟨e_v56, he_v56⟩
      store_step with CtorSpec.eo_to_5freal.construct s45 e_v56 (by rw [he_v56]; exact empty_args) hinv45 h64 as ⟨v56, s46, hinv46, h_v56⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 dropping h_v55 he_v56 e_v56 v55
      store_step with Store.apply_rep s46 v56 v2 _ _ hinv46 h64 h_v56 h_v2 (by ns_tac) (by ns_tac) as ⟨v57, s47, hinv47, h_v57⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 dropping h_v56 v56
      ite_done hinv47 hG with (eo_ite_true_rep _ hx_56 h_v57)
    · ite_branch hbv_56
      ite_done hinv45 hG with (eo_ite_false_rep _ hx_56 h_v2)
    · ite_branch hbv_56
      ite_stuck hinv45 hG with hx_56)
  store_step with h_ite_v58 as ⟨v58, s46, hinv46, h_v58⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 dropping h_ite_v58 h_v2 h_v55 hinv45 s45 v2 v55
  store_step with ih.eo__24eo_5ftypeof s46 v58 _ hinv46 h64 (hG.rem hrem) h_v58 as ⟨v59, s47, hinv47, h_v59⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 h_v52 dropping h_v58 hinv46 s46 v58
  store_step with ih.eo__24eo_5fnil s47 v52 v59 _ _ hinv47 h64 (hG.rem hrem) h_v52 h_v59 as ⟨v60, s48, hinv48, h_v60⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 h_v51 dropping h_v52 h_v59 hinv47 s47 v52 v59
  store_step with Store.apply_mk_rep s48 v51 v60 _ _ hinv48 h64 h_v51 h_v60 as ⟨v61, s49, hinv49, h_v61⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v36 h_v44 dropping h_v51 h_v60 hinv48 s48 v51 v60
  store_step with Store.apply_mk_rep s49 v44 v61 _ _ hinv49 h64 h_v44 h_v61 as ⟨v62, s50, hinv50, h_v62⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v36 dropping h_v44 h_v61 hinv49 s49 v44 v61
  store_step with Store.apply_mk_rep s50 v36 v62 _ _ hinv50 h64 h_v36 h_v62 as ⟨v63, s51, hinv51, h_v63⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 dropping h_v36 h_v62 hinv50 s50 v36 v62
  store_step with ih.eo__24eo_5ftypeof s51 v5 _ hinv51 h64 (hG.rem hrem) h_v5 as ⟨v64, s52, hinv52, h_v64⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v63 dropping hinv51 s51
  step as ⟨e_v65, he_v65⟩
  store_step with CtorSpec.eo_Int.construct s52 e_v65 (by rw [he_v65]; exact empty_args) hinv52 h64 as ⟨v65, s53, hinv53, h_v65⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v63 h_v64 dropping he_v65 hinv52 e_v65 s52
  step as ⟨e_v66, he_v66⟩
  store_step with Store.builtin_spec_eq s53 e_v66 (by rw [he_v66]; rfl) h_v64 h_v65 hinv53 h64 as ⟨v66, s54, hinv54, h_v66⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v63 dropping h_v64 h_v65 he_v66 hinv53 e_v66 s53 v64 v65
  have h_ite_v69 := (show if_16_eo__24arith_5freduction_5fpred s54 v66 v5 ⦃ r s' => s'.Inv ∧ s54.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_16_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s54
    rcases Store.boolean_value_term h_v66 with ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩
    · ite_branch hbv_67
      step as ⟨e_v67, he_v67⟩
      store_step with CtorSpec.eo_to_5freal.construct s54 e_v67 (by rw [he_v67]; exact empty_args) hinv54 h64 as ⟨v67, s55, hinv55, h_v67⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v63 dropping h_v66 he_v67 e_v67 v66
      store_step with Store.apply_rep s55 v67 v5 _ _ hinv55 h64 h_v67 h_v5 (by ns_tac) (by ns_tac) as ⟨v68, s56, hinv56, h_v68⟩ growing hG carrying h_v5 h_v19 h_v20 h_v35 h_v63 dropping h_v67 v67
      ite_done hinv56 hG with (eo_ite_true_rep _ hx_67 h_v68)
    · ite_branch hbv_67
      ite_done hinv54 hG with (eo_ite_false_rep _ hx_67 h_v5)
    · ite_branch hbv_67
      ite_stuck hinv54 hG with hx_67)
  store_step with h_ite_v69 as ⟨v69, s55, hinv55, h_v69⟩ growing hG carrying h_v19 h_v20 h_v35 h_v63 dropping h_ite_v69 h_v5 h_v66 hinv54 s54 v5 v66
  store_step with Store.apply_mk_rep s55 v63 v69 _ _ hinv55 h64 h_v63 h_v69 as ⟨v70, s56, hinv56, h_v70⟩ growing hG carrying h_v19 h_v20 h_v35 dropping h_v63 h_v69 hinv55 s55 v63 v69
  store_step with Store.apply_mk_rep s56 v35 v70 _ _ hinv56 h64 h_v35 h_v70 as ⟨v71, s57, hinv57, h_v71⟩ growing hG carrying h_v19 h_v20 dropping h_v35 h_v70 hinv56 s56 v35 v70
  store_step with Store.apply_mk_rep s57 v20 v71 _ _ hinv57 h64 h_v20 h_v71 as ⟨v72, s58, hinv58, h_v72⟩ growing hG carrying h_v19 dropping h_v20 h_v71 hinv57 s57 v20 v71
  store_step with Store.literal_boolean_spec s58 true hinv58 h64 as ⟨v73, s59, hinv59, h_v73⟩ growing hG carrying h_v19 h_v72 dropping hinv58 s58
  store_step with Store.apply_mk_rep s59 v72 v73 _ _ hinv59 h64 h_v72 h_v73 as ⟨v74, s60, hinv60, h_v74⟩ growing hG carrying h_v19 dropping h_v72 h_v73 hinv59 s59 v72 v73
  store_step with Store.apply_mk_rep s60 v19 v74 _ _ hinv60 h64 h_v19 h_v74 as ⟨v75, s61, hinv61, h_v75⟩ growing hG carrying dropping h_v19 h_v74 hinv60 s60 v19 v74
  case_done hinv61 hG with h_v75 in EoCases.__arith_reduction_pred.case_5 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 5520000 in
theorem case_6_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_6_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_6 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_6 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_6
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_6
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_6
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40purify.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping he_v13 hinv7 e_v13 s7
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s8 e_v14 (by rw [he_v14]; exact empty_args) hinv8 h64 as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v13 dropping he_v14 hinv8 e_v14 s8
  store_step with Store.apply_rep s9 v14 v5 _ _ hinv9 h64 h_v14 h_v5 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v13 dropping h_v14 hinv9 s9 v14
  store_step with Store.apply_rep s10 v15 v2 _ _ hinv10 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v13 dropping h_v15 hinv10 s10 v15
  store_step with Store.apply_rep s11 v13 v16 _ _ hinv11 h64 h_v13 h_v16 (by ns_tac) (by ns_tac) as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping h_v13 h_v16 hinv11 s11 v13 v16
  store_step with Store.apply_rep s12 v12 v17 _ _ hinv12 h64 h_v12 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v12 h_v17 hinv12 s12 v12 v17
  store_step with Store.apply_rep s13 v7 v18 _ _ hinv13 h64 h_v7 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 dropping h_v18 h_v7 hinv13 s13 v18 v7
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_and.construct s14 e_v20 (by rw [he_v20]; exact empty_args) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v19 dropping he_v20 hinv14 e_v20 s14
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_is_z s15 e_v21 (by rw [he_v21]; rfl) h_v2 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping he_v21 hinv15 e_v21 s15
  have h_ite_v185 := (show if_36_eo__24arith_5freduction_5fpred s16 v21 v2 v5 ⦃ r s' => s'.Inv ∧ s16.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_36_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s16
    rcases Store.boolean_value_term h_v21 with ⟨hx_22, hbv_22⟩ | ⟨hx_22, hbv_22⟩ | ⟨hx_22, hbv_22⟩
    · ite_branch hbv_22
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v21 v21
      step as ⟨e_v23, he_v23⟩
      store_step with Store.builtin_spec_eq s17 e_v23 (by rw [he_v23]; rfl) h_v2 h_v22 hinv17 h64 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v22 he_v23 e_v23 v22
      store_step with Store.literal_boolean_spec s18 false hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v23 dropping
      have h_req_v73 := (show requires_26_eo__24arith_5freduction_5fpred s19 v23 v24 v2 v5 ⦃ r s' => s'.Inv ∧ s19.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold requires_26_eo__24arith_5freduction_5fpred
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s19
        req_same v23 v24 with h_v23 h_v24 using hinv19 hG
        req_stuck h_v23 as hq_v23 using hinv19 hG
        step as ⟨e_v25, he_v25⟩
        store_step with CtorSpec.eo_and.construct s19 e_v25 (by rw [he_v25]; exact empty_args) hinv19 h64 as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v23 h_v24 he_v25 e_v25 v23 v24
        step as ⟨e_v26, he_v26⟩
        store_step with CtorSpec.eo__3c_3d.construct s20 e_v26 (by rw [he_v26]; exact empty_args) hinv20 h64 as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 dropping he_v26 e_v26
        step as ⟨e_v27, he_v27⟩
        store_step with CtorSpec.eo__2a.construct s21 e_v27 (by rw [he_v27]; exact empty_args) hinv21 h64 as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 dropping he_v27 e_v27
        store_step with Store.apply_rep s22 v27 v2 _ _ hinv22 h64 h_v27 h_v2 (by ns_tac) (by ns_tac) as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 dropping h_v27 v27
        step as ⟨e_v29, he_v29⟩
        store_step with CtorSpec.eo__2a.construct s23 e_v29 (by rw [he_v29]; exact empty_args) hinv23 h64 as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 dropping he_v29 e_v29
        step as ⟨e_v30, he_v30⟩
        store_step with CtorSpec.eo__40purify.construct s24 e_v30 (by rw [he_v30]; exact empty_args) hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 h_v29 dropping he_v30 e_v30
        step as ⟨e_v31, he_v31⟩
        store_step with CtorSpec.eo_div_5ftotal.construct s25 e_v31 (by rw [he_v31]; exact empty_args) hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 h_v29 h_v30 dropping he_v31 e_v31
        store_step with Store.apply_rep s26 v31 v5 _ _ hinv26 h64 h_v31 h_v5 (by ns_tac) (by ns_tac) as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 h_v29 h_v30 dropping h_v31 v31
        store_step with Store.apply_rep s27 v32 v2 _ _ hinv27 h64 h_v32 h_v2 (by ns_tac) (by ns_tac) as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 h_v29 h_v30 dropping h_v32 v32
        store_step with Store.apply_rep s28 v30 v33 _ _ hinv28 h64 h_v30 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 h_v29 dropping h_v30 h_v33 v30 v33
        store_step with Store.apply_rep s29 v29 v34 _ _ hinv29 h64 h_v29 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 dropping h_v29 h_v34 v29 v34
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s30 1#u32 (1) (by scalar_tac) hinv30 h64 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 h_v35 dropping
        store_step with Store.apply_rep s31 v35 v36 _ _ hinv31 h64 h_v35 h_v36 (by ns_tac) (by ns_tac) as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 h_v28 dropping h_v35 h_v36 v35 v36
        store_step with Store.apply_rep s32 v28 v37 _ _ hinv32 h64 h_v28 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 h_v26 dropping h_v28 h_v37 v28 v37
        store_step with Store.apply_rep s33 v26 v38 _ _ hinv33 h64 h_v26 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 dropping h_v26 h_v38 v26 v38
        store_step with Store.apply_rep s34 v39 v5 _ _ hinv34 h64 h_v39 h_v5 (by ns_tac) (by ns_tac) as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v25 dropping h_v39 v39
        store_step with Store.apply_rep s35 v25 v40 _ _ hinv35 h64 h_v25 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v25 h_v40 v25 v40
        step as ⟨e_v42, he_v42⟩
        store_step with CtorSpec.eo_and.construct s36 e_v42 (by rw [he_v42]; exact empty_args) hinv36 h64 as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 dropping he_v42 e_v42
        step as ⟨e_v43, he_v43⟩
        store_step with CtorSpec.eo__3c.construct s37 e_v43 (by rw [he_v43]; exact empty_args) hinv37 h64 as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 dropping he_v43 e_v43
        store_step with Store.apply_rep s38 v43 v5 _ _ hinv38 h64 h_v43 h_v5 (by ns_tac) (by ns_tac) as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 dropping h_v43 v43
        step as ⟨e_v45, he_v45⟩
        store_step with CtorSpec.eo__2a.construct s39 e_v45 (by rw [he_v45]; exact empty_args) hinv39 h64 as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 dropping he_v45 e_v45
        store_step with Store.apply_rep s40 v45 v2 _ _ hinv40 h64 h_v45 h_v2 (by ns_tac) (by ns_tac) as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 dropping h_v45 v45
        step as ⟨e_v47, he_v47⟩
        store_step with CtorSpec.eo__2a.construct s41 e_v47 (by rw [he_v47]; exact empty_args) hinv41 h64 as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 dropping he_v47 e_v47
        step as ⟨e_v48, he_v48⟩
        store_step with CtorSpec.eo__2b.construct s42 e_v48 (by rw [he_v48]; exact empty_args) hinv42 h64 as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 dropping he_v48 e_v48
        step as ⟨e_v49, he_v49⟩
        store_step with CtorSpec.eo__40purify.construct s43 e_v49 (by rw [he_v49]; exact empty_args) hinv43 h64 as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v48 dropping he_v49 e_v49
        step as ⟨e_v50, he_v50⟩
        store_step with CtorSpec.eo_div_5ftotal.construct s44 e_v50 (by rw [he_v50]; exact empty_args) hinv44 h64 as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v48 h_v49 dropping he_v50 e_v50
        store_step with Store.apply_rep s45 v50 v5 _ _ hinv45 h64 h_v50 h_v5 (by ns_tac) (by ns_tac) as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v48 h_v49 dropping h_v50 v50
        store_step with Store.apply_rep s46 v51 v2 _ _ hinv46 h64 h_v51 h_v2 (by ns_tac) (by ns_tac) as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v48 h_v49 dropping h_v51 v51
        store_step with Store.apply_rep s47 v49 v52 _ _ hinv47 h64 h_v49 h_v52 (by ns_tac) (by ns_tac) as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v48 dropping h_v49 h_v52 v49 v52
        store_step with Store.apply_rep s48 v48 v53 _ _ hinv48 h64 h_v48 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 dropping h_v48 h_v53 v48 v53
        step as ⟨e_v55, he_v55⟩
        store_step with CtorSpec.eo__2b.construct s49 e_v55 (by rw [he_v55]; exact empty_args) hinv49 h64 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 dropping he_v55 e_v55
        step as ⟨e_v56, he_v56⟩
        store_step with Store.builtin_spec_is_neg s50 e_v56 (by rw [he_v56]; rfl) h_v2 hinv50 h64 as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 h_v55 dropping he_v56 e_v56
        have h_ite_v59 := (show if_22_eo__24arith_5freduction_5fpred s51 v56 ⦃ r s' => s'.Inv ∧ s51.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
          unfold if_22_eo__24arith_5freduction_5fpred
          have hrem := (hG.rem hrem)
          have hG := Store.Grows.refl s51
          rcases Store.boolean_value_term h_v56 with ⟨hx_57, hbv_57⟩ | ⟨hx_57, hbv_57⟩ | ⟨hx_57, hbv_57⟩
          · ite_branch hbv_57
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s51 1#u32 (-1) (by scalar_tac) hinv51 h64 as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 h_v55 dropping h_v56 v56
            ite_done hinv52 hG with (eo_ite_true_rep _ hx_57 h_v57)
          · ite_branch hbv_57
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s51 1#u32 (1) (by scalar_tac) hinv51 h64 as ⟨v58, s52, hinv52, h_v58⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 h_v55 dropping h_v56 v56
            ite_done hinv52 hG with (eo_ite_false_rep _ hx_57 h_v58)
          · ite_branch hbv_57
            ite_stuck hinv51 hG with hx_57)
        store_step with h_ite_v59 as ⟨v59, s52, hinv52, h_v59⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 h_v55 dropping h_ite_v59 h_v56 v56
        store_step with Store.apply_mk_rep s52 v55 v59 _ _ hinv52 h64 h_v55 h_v59 as ⟨v60, s53, hinv53, h_v60⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 dropping h_v55 h_v59 v55 v59
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s53 0#u32 (0) (by scalar_tac) hinv53 h64 as ⟨v61, s54, hinv54, h_v61⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 h_v60 dropping
        store_step with Store.apply_mk_rep s54 v60 v61 _ _ hinv54 h64 h_v60 h_v61 as ⟨v62, s55, hinv55, h_v62⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 h_v54 dropping h_v60 h_v61 v60 v61
        store_step with Store.apply_mk_rep s55 v54 v62 _ _ hinv55 h64 h_v54 h_v62 as ⟨v63, s56, hinv56, h_v63⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v47 dropping h_v54 h_v62 v54 v62
        store_step with Store.apply_mk_rep s56 v47 v63 _ _ hinv56 h64 h_v47 h_v63 as ⟨v64, s57, hinv57, h_v64⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 dropping h_v47 h_v63 v47 v63
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s57 1#u32 (1) (by scalar_tac) hinv57 h64 as ⟨v65, s58, hinv58, h_v65⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 h_v64 dropping
        store_step with Store.apply_mk_rep s58 v64 v65 _ _ hinv58 h64 h_v64 h_v65 as ⟨v66, s59, hinv59, h_v66⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 h_v46 dropping h_v64 h_v65 v64 v65
        store_step with Store.apply_mk_rep s59 v46 v66 _ _ hinv59 h64 h_v46 h_v66 as ⟨v67, s60, hinv60, h_v67⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 h_v44 dropping h_v46 h_v66 v46 v66
        store_step with Store.apply_mk_rep s60 v44 v67 _ _ hinv60 h64 h_v44 h_v67 as ⟨v68, s61, hinv61, h_v68⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v42 dropping h_v44 h_v67 v44 v67
        store_step with Store.apply_mk_rep s61 v42 v68 _ _ hinv61 h64 h_v42 h_v68 as ⟨v69, s62, hinv62, h_v69⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 dropping h_v42 h_v68 v42 v68
        store_step with Store.literal_boolean_spec s62 true hinv62 h64 as ⟨v70, s63, hinv63, h_v70⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 h_v69 dropping
        store_step with Store.apply_mk_rep s63 v69 v70 _ _ hinv63 h64 h_v69 h_v70 as ⟨v71, s64, hinv64, h_v71⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v41 dropping h_v69 h_v70 v69 v70
        store_step with Store.apply_mk_rep s64 v41 v71 _ _ hinv64 h64 h_v41 h_v71 as ⟨v72, s65, hinv65, h_v72⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v41 h_v71 v41 v71
        req_done hinv65 hG with h_v72 using hq_v23)
      store_step with h_req_v73 as ⟨v73, s66, hinv66, h_v73⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_req_v73 h_v23 h_v24 v23 v24
      ite_done hinv66 hG with (eo_ite_true_rep _ hx_22 h_v73)
    · ite_branch hbv_22
      step as ⟨e_v74, he_v74⟩
      store_step with CtorSpec.eo_and.construct s16 e_v74 (by rw [he_v74]; exact empty_args) hinv16 h64 as ⟨v74, s17, hinv17, h_v74⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v21 he_v74 e_v74 v21
      step as ⟨e_v75, he_v75⟩
      store_step with CtorSpec.eo__3d_3e.construct s17 e_v75 (by rw [he_v75]; exact empty_args) hinv17 h64 as ⟨v75, s18, hinv18, h_v75⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 dropping he_v75 e_v75
      step as ⟨e_v76, he_v76⟩
      store_step with CtorSpec.eo__3e.construct s18 e_v76 (by rw [he_v76]; exact empty_args) hinv18 h64 as ⟨v76, s19, hinv19, h_v76⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v75 dropping he_v76 e_v76
      store_step with Store.apply_rep s19 v76 v2 _ _ hinv19 h64 h_v76 h_v2 (by ns_tac) (by ns_tac) as ⟨v77, s20, hinv20, h_v77⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v75 dropping h_v76 v76
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s20 0#u32 (0) (by scalar_tac) hinv20 h64 as ⟨v78, s21, hinv21, h_v78⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v75 h_v77 dropping
      store_step with Store.apply_rep s21 v77 v78 _ _ hinv21 h64 h_v77 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s22, hinv22, h_v79⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v75 dropping h_v77 h_v78 v77 v78
      store_step with Store.apply_rep s22 v75 v79 _ _ hinv22 h64 h_v75 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s23, hinv23, h_v80⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 dropping h_v75 h_v79 hinv22 s22 v75 v79
      step as ⟨e_v81, he_v81⟩
      store_step with CtorSpec.eo_and.construct s23 e_v81 (by rw [he_v81]; exact empty_args) hinv23 h64 as ⟨v81, s24, hinv24, h_v81⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 dropping he_v81 hinv23 e_v81 s23
      step as ⟨e_v82, he_v82⟩
      store_step with CtorSpec.eo__3c_3d.construct s24 e_v82 (by rw [he_v82]; exact empty_args) hinv24 h64 as ⟨v82, s25, hinv25, h_v82⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 dropping he_v82 hinv24 e_v82 s24
      step as ⟨e_v83, he_v83⟩
      store_step with CtorSpec.eo__2a.construct s25 e_v83 (by rw [he_v83]; exact empty_args) hinv25 h64 as ⟨v83, s26, hinv26, h_v83⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 dropping he_v83 hinv25 e_v83 s25
      store_step with Store.apply_rep s26 v83 v2 _ _ hinv26 h64 h_v83 h_v2 (by ns_tac) (by ns_tac) as ⟨v84, s27, hinv27, h_v84⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 dropping h_v83 hinv26 s26 v83
      step as ⟨e_v85, he_v85⟩
      store_step with CtorSpec.eo__2a.construct s27 e_v85 (by rw [he_v85]; exact empty_args) hinv27 h64 as ⟨v85, s28, hinv28, h_v85⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 dropping he_v85 hinv27 e_v85 s27
      step as ⟨e_v86, he_v86⟩
      store_step with CtorSpec.eo__40purify.construct s28 e_v86 (by rw [he_v86]; exact empty_args) hinv28 h64 as ⟨v86, s29, hinv29, h_v86⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 h_v85 dropping he_v86 hinv28 e_v86 s28
      step as ⟨e_v87, he_v87⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s29 e_v87 (by rw [he_v87]; exact empty_args) hinv29 h64 as ⟨v87, s30, hinv30, h_v87⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 dropping he_v87 hinv29 e_v87 s29
      store_step with Store.apply_rep s30 v87 v5 _ _ hinv30 h64 h_v87 h_v5 (by ns_tac) (by ns_tac) as ⟨v88, s31, hinv31, h_v88⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 dropping h_v87 hinv30 s30 v87
      store_step with Store.apply_rep s31 v88 v2 _ _ hinv31 h64 h_v88 h_v2 (by ns_tac) (by ns_tac) as ⟨v89, s32, hinv32, h_v89⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 h_v85 h_v86 dropping h_v88 hinv31 s31 v88
      store_step with Store.apply_rep s32 v86 v89 _ _ hinv32 h64 h_v86 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s33, hinv33, h_v90⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 h_v85 dropping h_v86 h_v89 hinv32 s32 v86 v89
      store_step with Store.apply_rep s33 v85 v90 _ _ hinv33 h64 h_v85 h_v90 (by ns_tac) (by ns_tac) as ⟨v91, s34, hinv34, h_v91⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 dropping h_v85 h_v90 hinv33 s33 v85 v90
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s34 1#u32 (1) (by scalar_tac) hinv34 h64 as ⟨v92, s35, hinv35, h_v92⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 h_v91 dropping hinv34 s34
      store_step with Store.apply_rep s35 v91 v92 _ _ hinv35 h64 h_v91 h_v92 (by ns_tac) (by ns_tac) as ⟨v93, s36, hinv36, h_v93⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 h_v84 dropping h_v91 h_v92 hinv35 s35 v91 v92
      store_step with Store.apply_rep s36 v84 v93 _ _ hinv36 h64 h_v84 h_v93 (by ns_tac) (by ns_tac) as ⟨v94, s37, hinv37, h_v94⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 h_v82 dropping h_v84 h_v93 hinv36 s36 v84 v93
      store_step with Store.apply_rep s37 v82 v94 _ _ hinv37 h64 h_v82 h_v94 (by ns_tac) (by ns_tac) as ⟨v95, s38, hinv38, h_v95⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 dropping h_v82 h_v94 hinv37 s37 v82 v94
      store_step with Store.apply_rep s38 v95 v5 _ _ hinv38 h64 h_v95 h_v5 (by ns_tac) (by ns_tac) as ⟨v96, s39, hinv39, h_v96⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v81 dropping h_v95 hinv38 s38 v95
      store_step with Store.apply_rep s39 v81 v96 _ _ hinv39 h64 h_v81 h_v96 (by ns_tac) (by ns_tac) as ⟨v97, s40, hinv40, h_v97⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 dropping h_v81 h_v96 hinv39 s39 v81 v96
      step as ⟨e_v98, he_v98⟩
      store_step with CtorSpec.eo_and.construct s40 e_v98 (by rw [he_v98]; exact empty_args) hinv40 h64 as ⟨v98, s41, hinv41, h_v98⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 dropping he_v98 hinv40 e_v98 s40
      step as ⟨e_v99, he_v99⟩
      store_step with CtorSpec.eo__3c.construct s41 e_v99 (by rw [he_v99]; exact empty_args) hinv41 h64 as ⟨v99, s42, hinv42, h_v99⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 dropping he_v99 hinv41 e_v99 s41
      store_step with Store.apply_rep s42 v99 v5 _ _ hinv42 h64 h_v99 h_v5 (by ns_tac) (by ns_tac) as ⟨v100, s43, hinv43, h_v100⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 dropping h_v99 hinv42 s42 v99
      step as ⟨e_v101, he_v101⟩
      store_step with CtorSpec.eo__2a.construct s43 e_v101 (by rw [he_v101]; exact empty_args) hinv43 h64 as ⟨v101, s44, hinv44, h_v101⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 dropping he_v101 hinv43 e_v101 s43
      store_step with Store.apply_rep s44 v101 v2 _ _ hinv44 h64 h_v101 h_v2 (by ns_tac) (by ns_tac) as ⟨v102, s45, hinv45, h_v102⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 dropping h_v101 hinv44 s44 v101
      step as ⟨e_v103, he_v103⟩
      store_step with CtorSpec.eo__2a.construct s45 e_v103 (by rw [he_v103]; exact empty_args) hinv45 h64 as ⟨v103, s46, hinv46, h_v103⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 dropping he_v103 hinv45 e_v103 s45
      step as ⟨e_v104, he_v104⟩
      store_step with CtorSpec.eo__2b.construct s46 e_v104 (by rw [he_v104]; exact empty_args) hinv46 h64 as ⟨v104, s47, hinv47, h_v104⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 dropping he_v104 hinv46 e_v104 s46
      step as ⟨e_v105, he_v105⟩
      store_step with CtorSpec.eo__40purify.construct s47 e_v105 (by rw [he_v105]; exact empty_args) hinv47 h64 as ⟨v105, s48, hinv48, h_v105⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v104 dropping he_v105 hinv47 e_v105 s47
      step as ⟨e_v106, he_v106⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s48 e_v106 (by rw [he_v106]; exact empty_args) hinv48 h64 as ⟨v106, s49, hinv49, h_v106⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v104 h_v105 dropping he_v106 hinv48 e_v106 s48
      store_step with Store.apply_rep s49 v106 v5 _ _ hinv49 h64 h_v106 h_v5 (by ns_tac) (by ns_tac) as ⟨v107, s50, hinv50, h_v107⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v104 h_v105 dropping h_v106 hinv49 s49 v106
      store_step with Store.apply_rep s50 v107 v2 _ _ hinv50 h64 h_v107 h_v2 (by ns_tac) (by ns_tac) as ⟨v108, s51, hinv51, h_v108⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v104 h_v105 dropping h_v107 hinv50 s50 v107
      store_step with Store.apply_rep s51 v105 v108 _ _ hinv51 h64 h_v105 h_v108 (by ns_tac) (by ns_tac) as ⟨v109, s52, hinv52, h_v109⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v104 dropping h_v105 h_v108 hinv51 s51 v105 v108
      store_step with Store.apply_rep s52 v104 v109 _ _ hinv52 h64 h_v104 h_v109 (by ns_tac) (by ns_tac) as ⟨v110, s53, hinv53, h_v110⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 dropping h_v104 h_v109 hinv52 s52 v104 v109
      step as ⟨e_v111, he_v111⟩
      store_step with CtorSpec.eo__2b.construct s53 e_v111 (by rw [he_v111]; exact empty_args) hinv53 h64 as ⟨v111, s54, hinv54, h_v111⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v110 dropping he_v111 hinv53 e_v111 s53
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s54 1#u32 (1) (by scalar_tac) hinv54 h64 as ⟨v112, s55, hinv55, h_v112⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v110 h_v111 dropping hinv54 s54
      store_step with Store.apply_rep s55 v111 v112 _ _ hinv55 h64 h_v111 h_v112 (by ns_tac) (by ns_tac) as ⟨v113, s56, hinv56, h_v113⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v110 dropping h_v111 h_v112 hinv55 s55 v111 v112
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s56 0#u32 (0) (by scalar_tac) hinv56 h64 as ⟨v114, s57, hinv57, h_v114⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v110 h_v113 dropping hinv56 s56
      store_step with Store.apply_rep s57 v113 v114 _ _ hinv57 h64 h_v113 h_v114 (by ns_tac) (by ns_tac) as ⟨v115, s58, hinv58, h_v115⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 h_v110 dropping h_v113 h_v114 hinv57 s57 v113 v114
      store_step with Store.apply_rep s58 v110 v115 _ _ hinv58 h64 h_v110 h_v115 (by ns_tac) (by ns_tac) as ⟨v116, s59, hinv59, h_v116⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v103 dropping h_v110 h_v115 hinv58 s58 v110 v115
      store_step with Store.apply_rep s59 v103 v116 _ _ hinv59 h64 h_v103 h_v116 (by ns_tac) (by ns_tac) as ⟨v117, s60, hinv60, h_v117⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 dropping h_v103 h_v116 hinv59 s59 v103 v116
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s60 1#u32 (1) (by scalar_tac) hinv60 h64 as ⟨v118, s61, hinv61, h_v118⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 h_v117 dropping hinv60 s60
      store_step with Store.apply_rep s61 v117 v118 _ _ hinv61 h64 h_v117 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s62, hinv62, h_v119⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 h_v102 dropping h_v117 h_v118 hinv61 s61 v117 v118
      store_step with Store.apply_rep s62 v102 v119 _ _ hinv62 h64 h_v102 h_v119 (by ns_tac) (by ns_tac) as ⟨v120, s63, hinv63, h_v120⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 h_v100 dropping h_v102 h_v119 hinv62 s62 v102 v119
      store_step with Store.apply_rep s63 v100 v120 _ _ hinv63 h64 h_v100 h_v120 (by ns_tac) (by ns_tac) as ⟨v121, s64, hinv64, h_v121⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v98 dropping h_v100 h_v120 hinv63 s63 v100 v120
      store_step with Store.apply_rep s64 v98 v121 _ _ hinv64 h64 h_v98 h_v121 (by ns_tac) (by ns_tac) as ⟨v122, s65, hinv65, h_v122⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 dropping h_v121 h_v98 hinv64 s64 v121 v98
      store_step with Store.literal_boolean_spec s65 true hinv65 h64 as ⟨v123, s66, hinv66, h_v123⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 h_v122 dropping hinv65 s65
      store_step with Store.apply_rep s66 v122 v123 _ _ hinv66 h64 h_v122 h_v123 (by ns_tac) (by ns_tac) as ⟨v124, s67, hinv67, h_v124⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 h_v97 dropping h_v122 h_v123 hinv66 s66 v122 v123
      store_step with Store.apply_rep s67 v97 v124 _ _ hinv67 h64 h_v97 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s68, hinv68, h_v125⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 h_v80 dropping h_v124 h_v97 hinv67 s67 v124 v97
      store_step with Store.apply_rep s68 v80 v125 _ _ hinv68 h64 h_v80 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s69, hinv69, h_v126⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v74 dropping h_v125 h_v80 hinv68 s68 v125 v80
      store_step with Store.apply_rep s69 v74 v126 _ _ hinv69 h64 h_v74 h_v126 (by ns_tac) (by ns_tac) as ⟨v127, s70, hinv70, h_v127⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 dropping h_v126 h_v74 hinv69 s69 v126 v74
      step as ⟨e_v128, he_v128⟩
      store_step with CtorSpec.eo_and.construct s70 e_v128 (by rw [he_v128]; exact empty_args) hinv70 h64 as ⟨v128, s71, hinv71, h_v128⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 dropping he_v128 hinv70 e_v128 s70
      step as ⟨e_v129, he_v129⟩
      store_step with CtorSpec.eo__3d_3e.construct s71 e_v129 (by rw [he_v129]; exact empty_args) hinv71 h64 as ⟨v129, s72, hinv72, h_v129⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 dropping he_v129 hinv71 e_v129 s71
      step as ⟨e_v130, he_v130⟩
      store_step with CtorSpec.eo__3c.construct s72 e_v130 (by rw [he_v130]; exact empty_args) hinv72 h64 as ⟨v130, s73, hinv73, h_v130⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v129 dropping he_v130 hinv72 e_v130 s72
      store_step with Store.apply_rep s73 v130 v2 _ _ hinv73 h64 h_v130 h_v2 (by ns_tac) (by ns_tac) as ⟨v131, s74, hinv74, h_v131⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v129 dropping h_v130 hinv73 s73 v130
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s74 0#u32 (0) (by scalar_tac) hinv74 h64 as ⟨v132, s75, hinv75, h_v132⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v129 h_v131 dropping hinv74 s74
      store_step with Store.apply_rep s75 v131 v132 _ _ hinv75 h64 h_v131 h_v132 (by ns_tac) (by ns_tac) as ⟨v133, s76, hinv76, h_v133⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v129 dropping h_v131 h_v132 hinv75 s75 v131 v132
      store_step with Store.apply_rep s76 v129 v133 _ _ hinv76 h64 h_v129 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s77, hinv77, h_v134⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 dropping h_v129 h_v133 hinv76 s76 v129 v133
      step as ⟨e_v135, he_v135⟩
      store_step with CtorSpec.eo_and.construct s77 e_v135 (by rw [he_v135]; exact empty_args) hinv77 h64 as ⟨v135, s78, hinv78, h_v135⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 dropping he_v135 hinv77 e_v135 s77
      step as ⟨e_v136, he_v136⟩
      store_step with CtorSpec.eo__3c_3d.construct s78 e_v136 (by rw [he_v136]; exact empty_args) hinv78 h64 as ⟨v136, s79, hinv79, h_v136⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 dropping he_v136 hinv78 e_v136 s78
      step as ⟨e_v137, he_v137⟩
      store_step with CtorSpec.eo__2a.construct s79 e_v137 (by rw [he_v137]; exact empty_args) hinv79 h64 as ⟨v137, s80, hinv80, h_v137⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 dropping he_v137 hinv79 e_v137 s79
      store_step with Store.apply_rep s80 v137 v2 _ _ hinv80 h64 h_v137 h_v2 (by ns_tac) (by ns_tac) as ⟨v138, s81, hinv81, h_v138⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 dropping h_v137 hinv80 s80 v137
      step as ⟨e_v139, he_v139⟩
      store_step with CtorSpec.eo__2a.construct s81 e_v139 (by rw [he_v139]; exact empty_args) hinv81 h64 as ⟨v139, s82, hinv82, h_v139⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 dropping he_v139 hinv81 e_v139 s81
      step as ⟨e_v140, he_v140⟩
      store_step with CtorSpec.eo__40purify.construct s82 e_v140 (by rw [he_v140]; exact empty_args) hinv82 h64 as ⟨v140, s83, hinv83, h_v140⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 h_v139 dropping he_v140 hinv82 e_v140 s82
      step as ⟨e_v141, he_v141⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s83 e_v141 (by rw [he_v141]; exact empty_args) hinv83 h64 as ⟨v141, s84, hinv84, h_v141⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 h_v139 h_v140 dropping he_v141 hinv83 e_v141 s83
      store_step with Store.apply_rep s84 v141 v5 _ _ hinv84 h64 h_v141 h_v5 (by ns_tac) (by ns_tac) as ⟨v142, s85, hinv85, h_v142⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 h_v139 h_v140 dropping h_v141 hinv84 s84 v141
      store_step with Store.apply_rep s85 v142 v2 _ _ hinv85 h64 h_v142 h_v2 (by ns_tac) (by ns_tac) as ⟨v143, s86, hinv86, h_v143⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 h_v139 h_v140 dropping h_v142 hinv85 s85 v142
      store_step with Store.apply_rep s86 v140 v143 _ _ hinv86 h64 h_v140 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s87, hinv87, h_v144⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 h_v139 dropping h_v140 h_v143 hinv86 s86 v140 v143
      store_step with Store.apply_rep s87 v139 v144 _ _ hinv87 h64 h_v139 h_v144 (by ns_tac) (by ns_tac) as ⟨v145, s88, hinv88, h_v145⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 dropping h_v139 h_v144 hinv87 s87 v139 v144
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s88 1#u32 (1) (by scalar_tac) hinv88 h64 as ⟨v146, s89, hinv89, h_v146⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 h_v145 dropping hinv88 s88
      store_step with Store.apply_rep s89 v145 v146 _ _ hinv89 h64 h_v145 h_v146 (by ns_tac) (by ns_tac) as ⟨v147, s90, hinv90, h_v147⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 h_v138 dropping h_v145 h_v146 hinv89 s89 v145 v146
      store_step with Store.apply_rep s90 v138 v147 _ _ hinv90 h64 h_v138 h_v147 (by ns_tac) (by ns_tac) as ⟨v148, s91, hinv91, h_v148⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 h_v136 dropping h_v138 h_v147 hinv90 s90 v138 v147
      store_step with Store.apply_rep s91 v136 v148 _ _ hinv91 h64 h_v136 h_v148 (by ns_tac) (by ns_tac) as ⟨v149, s92, hinv92, h_v149⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 dropping h_v136 h_v148 hinv91 s91 v136 v148
      store_step with Store.apply_rep s92 v149 v5 _ _ hinv92 h64 h_v149 h_v5 (by ns_tac) (by ns_tac) as ⟨v150, s93, hinv93, h_v150⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v135 dropping h_v149 hinv92 s92 v149
      store_step with Store.apply_rep s93 v135 v150 _ _ hinv93 h64 h_v135 h_v150 (by ns_tac) (by ns_tac) as ⟨v151, s94, hinv94, h_v151⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 dropping h_v135 h_v150 hinv93 s93 v135 v150
      step as ⟨e_v152, he_v152⟩
      store_step with CtorSpec.eo_and.construct s94 e_v152 (by rw [he_v152]; exact empty_args) hinv94 h64 as ⟨v152, s95, hinv95, h_v152⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 dropping he_v152 hinv94 e_v152 s94
      step as ⟨e_v153, he_v153⟩
      store_step with CtorSpec.eo__3c.construct s95 e_v153 (by rw [he_v153]; exact empty_args) hinv95 h64 as ⟨v153, s96, hinv96, h_v153⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 dropping he_v153 hinv95 e_v153 s95
      store_step with Store.apply_rep s96 v153 v5 _ _ hinv96 h64 h_v153 h_v5 (by ns_tac) (by ns_tac) as ⟨v154, s97, hinv97, h_v154⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 dropping h_v153 hinv96 s96 v153
      step as ⟨e_v155, he_v155⟩
      store_step with CtorSpec.eo__2a.construct s97 e_v155 (by rw [he_v155]; exact empty_args) hinv97 h64 as ⟨v155, s98, hinv98, h_v155⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 dropping he_v155 hinv97 e_v155 s97
      store_step with Store.apply_rep s98 v155 v2 _ _ hinv98 h64 h_v155 h_v2 (by ns_tac) (by ns_tac) as ⟨v156, s99, hinv99, h_v156⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 dropping h_v155 hinv98 s98 v155
      step as ⟨e_v157, he_v157⟩
      store_step with CtorSpec.eo__2a.construct s99 e_v157 (by rw [he_v157]; exact empty_args) hinv99 h64 as ⟨v157, s100, hinv100, h_v157⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 dropping he_v157 hinv99 e_v157 s99
      step as ⟨e_v158, he_v158⟩
      store_step with CtorSpec.eo__2b.construct s100 e_v158 (by rw [he_v158]; exact empty_args) hinv100 h64 as ⟨v158, s101, hinv101, h_v158⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 dropping he_v158 hinv100 e_v158 s100
      step as ⟨e_v159, he_v159⟩
      store_step with CtorSpec.eo__40purify.construct s101 e_v159 (by rw [he_v159]; exact empty_args) hinv101 h64 as ⟨v159, s102, hinv102, h_v159⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v158 dropping he_v159 hinv101 e_v159 s101
      step as ⟨e_v160, he_v160⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s102 e_v160 (by rw [he_v160]; exact empty_args) hinv102 h64 as ⟨v160, s103, hinv103, h_v160⟩ growing hG carrying h_v2 h_v5 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v158 h_v159 dropping he_v160 hinv102 e_v160 s102
      store_step with Store.apply_rep s103 v160 v5 _ _ hinv103 h64 h_v160 h_v5 (by ns_tac) (by ns_tac) as ⟨v161, s104, hinv104, h_v161⟩ growing hG carrying h_v2 h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v158 h_v159 dropping h_v160 h_v5 hinv103 s103 v160 v5
      store_step with Store.apply_rep s104 v161 v2 _ _ hinv104 h64 h_v161 h_v2 (by ns_tac) (by ns_tac) as ⟨v162, s105, hinv105, h_v162⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v158 h_v159 dropping h_v161 h_v2 hinv104 s104 v161 v2
      store_step with Store.apply_rep s105 v159 v162 _ _ hinv105 h64 h_v159 h_v162 (by ns_tac) (by ns_tac) as ⟨v163, s106, hinv106, h_v163⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v158 dropping h_v159 h_v162 hinv105 s105 v159 v162
      store_step with Store.apply_rep s106 v158 v163 _ _ hinv106 h64 h_v158 h_v163 (by ns_tac) (by ns_tac) as ⟨v164, s107, hinv107, h_v164⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 dropping h_v158 h_v163 hinv106 s106 v158 v163
      step as ⟨e_v165, he_v165⟩
      store_step with CtorSpec.eo__2b.construct s107 e_v165 (by rw [he_v165]; exact empty_args) hinv107 h64 as ⟨v165, s108, hinv108, h_v165⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v164 dropping he_v165 hinv107 e_v165 s107
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s108 1#u32 (-1) (by scalar_tac) hinv108 h64 as ⟨v166, s109, hinv109, h_v166⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v164 h_v165 dropping hinv108 s108
      store_step with Store.apply_rep s109 v165 v166 _ _ hinv109 h64 h_v165 h_v166 (by ns_tac) (by ns_tac) as ⟨v167, s110, hinv110, h_v167⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v164 dropping h_v165 h_v166 hinv109 s109 v165 v166
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s110 0#u32 (0) (by scalar_tac) hinv110 h64 as ⟨v168, s111, hinv111, h_v168⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v164 h_v167 dropping hinv110 s110
      store_step with Store.apply_rep s111 v167 v168 _ _ hinv111 h64 h_v167 h_v168 (by ns_tac) (by ns_tac) as ⟨v169, s112, hinv112, h_v169⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 h_v164 dropping h_v167 h_v168 hinv111 s111 v167 v168
      store_step with Store.apply_rep s112 v164 v169 _ _ hinv112 h64 h_v164 h_v169 (by ns_tac) (by ns_tac) as ⟨v170, s113, hinv113, h_v170⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v157 dropping h_v164 h_v169 hinv112 s112 v164 v169
      store_step with Store.apply_rep s113 v157 v170 _ _ hinv113 h64 h_v157 h_v170 (by ns_tac) (by ns_tac) as ⟨v171, s114, hinv114, h_v171⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 dropping h_v157 h_v170 hinv113 s113 v157 v170
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s114 1#u32 (1) (by scalar_tac) hinv114 h64 as ⟨v172, s115, hinv115, h_v172⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 h_v171 dropping hinv114 s114
      store_step with Store.apply_rep s115 v171 v172 _ _ hinv115 h64 h_v171 h_v172 (by ns_tac) (by ns_tac) as ⟨v173, s116, hinv116, h_v173⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 h_v156 dropping h_v171 h_v172 hinv115 s115 v171 v172
      store_step with Store.apply_rep s116 v156 v173 _ _ hinv116 h64 h_v156 h_v173 (by ns_tac) (by ns_tac) as ⟨v174, s117, hinv117, h_v174⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 h_v154 dropping h_v156 h_v173 hinv116 s116 v156 v173
      store_step with Store.apply_rep s117 v154 v174 _ _ hinv117 h64 h_v154 h_v174 (by ns_tac) (by ns_tac) as ⟨v175, s118, hinv118, h_v175⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v152 dropping h_v154 h_v174 hinv117 s117 v154 v174
      store_step with Store.apply_rep s118 v152 v175 _ _ hinv118 h64 h_v152 h_v175 (by ns_tac) (by ns_tac) as ⟨v176, s119, hinv119, h_v176⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 dropping h_v152 h_v175 hinv118 s118 v152 v175
      store_step with Store.literal_boolean_spec s119 true hinv119 h64 as ⟨v177, s120, hinv120, h_v177⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 h_v176 dropping hinv119 s119
      store_step with Store.apply_rep s120 v176 v177 _ _ hinv120 h64 h_v176 h_v177 (by ns_tac) (by ns_tac) as ⟨v178, s121, hinv121, h_v178⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 h_v151 dropping h_v176 h_v177 hinv120 s120 v176 v177
      store_step with Store.apply_rep s121 v151 v178 _ _ hinv121 h64 h_v151 h_v178 (by ns_tac) (by ns_tac) as ⟨v179, s122, hinv122, h_v179⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 h_v134 dropping h_v151 h_v178 hinv121 s121 v151 v178
      store_step with Store.apply_rep s122 v134 v179 _ _ hinv122 h64 h_v134 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s123, hinv123, h_v180⟩ growing hG carrying h_v19 h_v20 h_v127 h_v128 dropping h_v134 h_v179 hinv122 s122 v134 v179
      store_step with Store.apply_rep s123 v128 v180 _ _ hinv123 h64 h_v128 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s124, hinv124, h_v181⟩ growing hG carrying h_v19 h_v20 h_v127 dropping h_v128 h_v180 hinv123 s123 v128 v180
      store_step with Store.literal_boolean_spec s124 true hinv124 h64 as ⟨v182, s125, hinv125, h_v182⟩ growing hG carrying h_v19 h_v20 h_v127 h_v181 dropping hinv124 s124
      store_step with Store.apply_rep s125 v181 v182 _ _ hinv125 h64 h_v181 h_v182 (by ns_tac) (by ns_tac) as ⟨v183, s126, hinv126, h_v183⟩ growing hG carrying h_v19 h_v20 h_v127 dropping h_v181 h_v182 hinv125 s125 v181 v182
      store_step with Store.apply_rep s126 v127 v183 _ _ hinv126 h64 h_v127 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s127, hinv127, h_v184⟩ growing hG carrying h_v19 h_v20 dropping h_v127 h_v183 hinv126 s126 v127 v183
      ite_done hinv127 hG with (eo_ite_false_rep _ hx_22 h_v184)
    · ite_branch hbv_22
      ite_stuck hinv16 hG with hx_22)
  store_step with h_ite_v185 as ⟨v185, s17, hinv17, h_v185⟩ growing hG carrying h_v19 h_v20 dropping h_ite_v185 h_v2 h_v21 h_v5 hinv16 s16 v2 v21 v5
  store_step with Store.apply_mk_rep s17 v20 v185 _ _ hinv17 h64 h_v20 h_v185 as ⟨v186, s18, hinv18, h_v186⟩ growing hG carrying h_v19 dropping h_v185 h_v20 hinv17 s17 v185 v20
  store_step with Store.literal_boolean_spec s18 true hinv18 h64 as ⟨v187, s19, hinv19, h_v187⟩ growing hG carrying h_v19 h_v186 dropping hinv18 s18
  store_step with Store.apply_mk_rep s19 v186 v187 _ _ hinv19 h64 h_v186 h_v187 as ⟨v188, s20, hinv20, h_v188⟩ growing hG carrying h_v19 dropping h_v186 h_v187 hinv19 s19 v186 v187
  store_step with Store.apply_mk_rep s20 v19 v188 _ _ hinv20 h64 h_v19 h_v188 as ⟨v189, s21, hinv21, h_v189⟩ growing hG carrying dropping h_v188 h_v19 hinv20 s20 v188 v19
  case_done hinv21 hG with h_v189 in EoCases.__arith_reduction_pred.case_6 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

set_option maxHeartbeats 5820000 in
theorem case_7_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_7_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_7 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_7
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_7
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_a0 h_v1 he_v6 e_v6 v1
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_7
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_and.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_v2 h_v5 dropping h_v4 h_v6 he_v7 hinv1 e_v7 s1 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_v2 h_v5 h_v7 dropping he_v8 hinv2 e_v8 s2
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo_mod_5ftotal.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping he_v9 hinv3 e_v9 s3
  store_step with Store.apply_rep s4 v9 v5 _ _ hinv4 h64 h_v9 h_v5 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v9 hinv4 s4 v9
  store_step with Store.apply_rep s5 v10 v2 _ _ hinv5 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_v2 h_v5 h_v7 h_v8 dropping h_v10 hinv5 s5 v10
  store_step with Store.apply_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v11 h_v8 hinv6 s6 v11 v8
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__2d.construct s7 e_v13 (by rw [he_v13]; exact empty_args) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping he_v13 hinv7 e_v13 s7
  store_step with Store.apply_rep s8 v13 v5 _ _ hinv8 h64 h_v13 h_v5 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping h_v13 hinv8 s8 v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__2a.construct s9 e_v15 (by rw [he_v15]; exact empty_args) hinv9 h64 as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 dropping he_v15 hinv9 e_v15 s9
  store_step with Store.apply_rep s10 v15 v2 _ _ hinv10 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 dropping h_v15 hinv10 s10 v15
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__2a.construct s11 e_v17 (by rw [he_v17]; exact empty_args) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 dropping he_v17 hinv11 e_v17 s11
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__40purify.construct s12 e_v18 (by rw [he_v18]; exact empty_args) hinv12 h64 as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 h_v17 dropping he_v18 hinv12 e_v18 s12
  step as ⟨e_v19, he_v19⟩
  store_step with CtorSpec.eo_div_5ftotal.construct s13 e_v19 (by rw [he_v19]; exact empty_args) hinv13 h64 as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 h_v17 h_v18 dropping he_v19 hinv13 e_v19 s13
  store_step with Store.apply_rep s14 v19 v5 _ _ hinv14 h64 h_v19 h_v5 (by ns_tac) (by ns_tac) as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 h_v17 h_v18 dropping h_v19 hinv14 s14 v19
  store_step with Store.apply_rep s15 v20 v2 _ _ hinv15 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 h_v17 h_v18 dropping h_v20 hinv15 s15 v20
  store_step with Store.apply_rep s16 v18 v21 _ _ hinv16 h64 h_v18 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 h_v17 dropping h_v18 h_v21 hinv16 s16 v18 v21
  store_step with Store.apply_rep s17 v17 v22 _ _ hinv17 h64 h_v17 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 dropping h_v17 h_v22 hinv17 s17 v17 v22
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s18 1#u32 (1) (by scalar_tac) hinv18 h64 as ⟨v24, s19, hinv19, h_v24⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 h_v23 dropping hinv18 s18
  store_step with Store.apply_rep s19 v23 v24 _ _ hinv19 h64 h_v23 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s20, hinv20, h_v25⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 h_v16 dropping h_v23 h_v24 hinv19 s19 v23 v24
  store_step with Store.apply_rep s20 v16 v25 _ _ hinv20 h64 h_v16 h_v25 (by ns_tac) (by ns_tac) as ⟨v26, s21, hinv21, h_v26⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 h_v14 dropping h_v16 h_v25 hinv20 s20 v16 v25
  store_step with Store.apply_rep s21 v14 v26 _ _ hinv21 h64 h_v14 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s22, hinv22, h_v27⟩ growing hG carrying h_v2 h_v5 h_v7 h_v12 dropping h_v14 h_v26 hinv21 s21 v14 v26
  store_step with Store.apply_rep s22 v12 v27 _ _ hinv22 h64 h_v12 h_v27 (by ns_tac) (by ns_tac) as ⟨v28, s23, hinv23, h_v28⟩ growing hG carrying h_v2 h_v5 h_v7 dropping h_v12 h_v27 hinv22 s22 v12 v27
  store_step with Store.apply_rep s23 v7 v28 _ _ hinv23 h64 h_v7 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s24, hinv24, h_v29⟩ growing hG carrying h_v2 h_v5 dropping h_v28 h_v7 hinv23 s23 v28 v7
  step as ⟨e_v30, he_v30⟩
  store_step with CtorSpec.eo_and.construct s24 e_v30 (by rw [he_v30]; exact empty_args) hinv24 h64 as ⟨v30, s25, hinv25, h_v30⟩ growing hG carrying h_v2 h_v5 h_v29 dropping he_v30 hinv24 e_v30 s24
  step as ⟨e_v31, he_v31⟩
  store_step with Store.builtin_spec_is_z s25 e_v31 (by rw [he_v31]; rfl) h_v2 hinv25 h64 as ⟨v31, s26, hinv26, h_v31⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping he_v31 hinv25 e_v31 s25
  have h_ite_v195 := (show if_52_eo__24arith_5freduction_5fpred s26 v31 v2 v5 ⦃ r s' => s'.Inv ∧ s26.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_52_eo__24arith_5freduction_5fpred
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s26
    rcases Store.boolean_value_term h_v31 with ⟨hx_32, hbv_32⟩ | ⟨hx_32, hbv_32⟩ | ⟨hx_32, hbv_32⟩
    · ite_branch hbv_32
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s26 0#u32 (0) (by scalar_tac) hinv26 h64 as ⟨v32, s27, hinv27, h_v32⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v31 v31
      step as ⟨e_v33, he_v33⟩
      store_step with Store.builtin_spec_eq s27 e_v33 (by rw [he_v33]; rfl) h_v2 h_v32 hinv27 h64 as ⟨v33, s28, hinv28, h_v33⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v32 he_v33 e_v33 v32
      store_step with Store.literal_boolean_spec s28 false hinv28 h64 as ⟨v34, s29, hinv29, h_v34⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v33 dropping
      have h_req_v83 := (show requires_42_eo__24arith_5freduction_5fpred s29 v33 v34 v2 v5 ⦃ r s' => s'.Inv ∧ s29.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_requires _ _ _) | core.result.Result.Err _ => True ⦄div from by
        unfold requires_42_eo__24arith_5freduction_5fpred
        have hrem := (hG.rem hrem)
        have hG := Store.Grows.refl s29
        req_same v33 v34 with h_v33 h_v34 using hinv29 hG
        req_stuck h_v33 as hq_v33 using hinv29 hG
        step as ⟨e_v35, he_v35⟩
        store_step with CtorSpec.eo_and.construct s29 e_v35 (by rw [he_v35]; exact empty_args) hinv29 h64 as ⟨v35, s30, hinv30, h_v35⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v33 h_v34 he_v35 e_v35 v33 v34
        step as ⟨e_v36, he_v36⟩
        store_step with CtorSpec.eo__3c_3d.construct s30 e_v36 (by rw [he_v36]; exact empty_args) hinv30 h64 as ⟨v36, s31, hinv31, h_v36⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 dropping he_v36 e_v36
        step as ⟨e_v37, he_v37⟩
        store_step with CtorSpec.eo__2a.construct s31 e_v37 (by rw [he_v37]; exact empty_args) hinv31 h64 as ⟨v37, s32, hinv32, h_v37⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 dropping he_v37 e_v37
        store_step with Store.apply_rep s32 v37 v2 _ _ hinv32 h64 h_v37 h_v2 (by ns_tac) (by ns_tac) as ⟨v38, s33, hinv33, h_v38⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 dropping h_v37 v37
        step as ⟨e_v39, he_v39⟩
        store_step with CtorSpec.eo__2a.construct s33 e_v39 (by rw [he_v39]; exact empty_args) hinv33 h64 as ⟨v39, s34, hinv34, h_v39⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 dropping he_v39 e_v39
        step as ⟨e_v40, he_v40⟩
        store_step with CtorSpec.eo__40purify.construct s34 e_v40 (by rw [he_v40]; exact empty_args) hinv34 h64 as ⟨v40, s35, hinv35, h_v40⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 h_v39 dropping he_v40 e_v40
        step as ⟨e_v41, he_v41⟩
        store_step with CtorSpec.eo_div_5ftotal.construct s35 e_v41 (by rw [he_v41]; exact empty_args) hinv35 h64 as ⟨v41, s36, hinv36, h_v41⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 h_v39 h_v40 dropping he_v41 e_v41
        store_step with Store.apply_rep s36 v41 v5 _ _ hinv36 h64 h_v41 h_v5 (by ns_tac) (by ns_tac) as ⟨v42, s37, hinv37, h_v42⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 h_v39 h_v40 dropping h_v41 v41
        store_step with Store.apply_rep s37 v42 v2 _ _ hinv37 h64 h_v42 h_v2 (by ns_tac) (by ns_tac) as ⟨v43, s38, hinv38, h_v43⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 h_v39 h_v40 dropping h_v42 v42
        store_step with Store.apply_rep s38 v40 v43 _ _ hinv38 h64 h_v40 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s39, hinv39, h_v44⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 h_v39 dropping h_v40 h_v43 v40 v43
        store_step with Store.apply_rep s39 v39 v44 _ _ hinv39 h64 h_v39 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s40, hinv40, h_v45⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 dropping h_v39 h_v44 v39 v44
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s40 1#u32 (1) (by scalar_tac) hinv40 h64 as ⟨v46, s41, hinv41, h_v46⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 h_v45 dropping
        store_step with Store.apply_rep s41 v45 v46 _ _ hinv41 h64 h_v45 h_v46 (by ns_tac) (by ns_tac) as ⟨v47, s42, hinv42, h_v47⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 h_v38 dropping h_v45 h_v46 v45 v46
        store_step with Store.apply_rep s42 v38 v47 _ _ hinv42 h64 h_v38 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s43, hinv43, h_v48⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 h_v36 dropping h_v38 h_v47 v38 v47
        store_step with Store.apply_rep s43 v36 v48 _ _ hinv43 h64 h_v36 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s44, hinv44, h_v49⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 dropping h_v36 h_v48 v36 v48
        store_step with Store.apply_rep s44 v49 v5 _ _ hinv44 h64 h_v49 h_v5 (by ns_tac) (by ns_tac) as ⟨v50, s45, hinv45, h_v50⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v35 dropping h_v49 v49
        store_step with Store.apply_rep s45 v35 v50 _ _ hinv45 h64 h_v35 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s46, hinv46, h_v51⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v35 h_v50 v35 v50
        step as ⟨e_v52, he_v52⟩
        store_step with CtorSpec.eo_and.construct s46 e_v52 (by rw [he_v52]; exact empty_args) hinv46 h64 as ⟨v52, s47, hinv47, h_v52⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 dropping he_v52 e_v52
        step as ⟨e_v53, he_v53⟩
        store_step with CtorSpec.eo__3c.construct s47 e_v53 (by rw [he_v53]; exact empty_args) hinv47 h64 as ⟨v53, s48, hinv48, h_v53⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 dropping he_v53 e_v53
        store_step with Store.apply_rep s48 v53 v5 _ _ hinv48 h64 h_v53 h_v5 (by ns_tac) (by ns_tac) as ⟨v54, s49, hinv49, h_v54⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 dropping h_v53 v53
        step as ⟨e_v55, he_v55⟩
        store_step with CtorSpec.eo__2a.construct s49 e_v55 (by rw [he_v55]; exact empty_args) hinv49 h64 as ⟨v55, s50, hinv50, h_v55⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 dropping he_v55 e_v55
        store_step with Store.apply_rep s50 v55 v2 _ _ hinv50 h64 h_v55 h_v2 (by ns_tac) (by ns_tac) as ⟨v56, s51, hinv51, h_v56⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 dropping h_v55 v55
        step as ⟨e_v57, he_v57⟩
        store_step with CtorSpec.eo__2a.construct s51 e_v57 (by rw [he_v57]; exact empty_args) hinv51 h64 as ⟨v57, s52, hinv52, h_v57⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 dropping he_v57 e_v57
        step as ⟨e_v58, he_v58⟩
        store_step with CtorSpec.eo__2b.construct s52 e_v58 (by rw [he_v58]; exact empty_args) hinv52 h64 as ⟨v58, s53, hinv53, h_v58⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 dropping he_v58 e_v58
        step as ⟨e_v59, he_v59⟩
        store_step with CtorSpec.eo__40purify.construct s53 e_v59 (by rw [he_v59]; exact empty_args) hinv53 h64 as ⟨v59, s54, hinv54, h_v59⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v58 dropping he_v59 e_v59
        step as ⟨e_v60, he_v60⟩
        store_step with CtorSpec.eo_div_5ftotal.construct s54 e_v60 (by rw [he_v60]; exact empty_args) hinv54 h64 as ⟨v60, s55, hinv55, h_v60⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v58 h_v59 dropping he_v60 e_v60
        store_step with Store.apply_rep s55 v60 v5 _ _ hinv55 h64 h_v60 h_v5 (by ns_tac) (by ns_tac) as ⟨v61, s56, hinv56, h_v61⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v58 h_v59 dropping h_v60 v60
        store_step with Store.apply_rep s56 v61 v2 _ _ hinv56 h64 h_v61 h_v2 (by ns_tac) (by ns_tac) as ⟨v62, s57, hinv57, h_v62⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v58 h_v59 dropping h_v61 v61
        store_step with Store.apply_rep s57 v59 v62 _ _ hinv57 h64 h_v59 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s58, hinv58, h_v63⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v58 dropping h_v59 h_v62 v59 v62
        store_step with Store.apply_rep s58 v58 v63 _ _ hinv58 h64 h_v58 h_v63 (by ns_tac) (by ns_tac) as ⟨v64, s59, hinv59, h_v64⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 dropping h_v58 h_v63 v58 v63
        step as ⟨e_v65, he_v65⟩
        store_step with CtorSpec.eo__2b.construct s59 e_v65 (by rw [he_v65]; exact empty_args) hinv59 h64 as ⟨v65, s60, hinv60, h_v65⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 dropping he_v65 e_v65
        step as ⟨e_v66, he_v66⟩
        store_step with Store.builtin_spec_is_neg s60 e_v66 (by rw [he_v66]; rfl) h_v2 hinv60 h64 as ⟨v66, s61, hinv61, h_v66⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 h_v65 dropping he_v66 e_v66
        have h_ite_v69 := (show if_38_eo__24arith_5freduction_5fpred s61 v66 ⦃ r s' => s'.Inv ∧ s61.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
          unfold if_38_eo__24arith_5freduction_5fpred
          have hrem := (hG.rem hrem)
          have hG := Store.Grows.refl s61
          rcases Store.boolean_value_term h_v66 with ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩ | ⟨hx_67, hbv_67⟩
          · ite_branch hbv_67
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_neg_u32_spec s61 1#u32 (-1) (by scalar_tac) hinv61 h64 as ⟨v67, s62, hinv62, h_v67⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 h_v65 dropping h_v66 v66
            ite_done hinv62 hG with (eo_ite_true_rep _ hx_67 h_v67)
          · ite_branch hbv_67
            try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
            store_step with Store.literal_int_u32_spec s61 1#u32 (1) (by scalar_tac) hinv61 h64 as ⟨v68, s62, hinv62, h_v68⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 h_v65 dropping h_v66 v66
            ite_done hinv62 hG with (eo_ite_false_rep _ hx_67 h_v68)
          · ite_branch hbv_67
            ite_stuck hinv61 hG with hx_67)
        store_step with h_ite_v69 as ⟨v69, s62, hinv62, h_v69⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 h_v65 dropping h_ite_v69 h_v66 v66
        store_step with Store.apply_mk_rep s62 v65 v69 _ _ hinv62 h64 h_v65 h_v69 as ⟨v70, s63, hinv63, h_v70⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 dropping h_v65 h_v69 v65 v69
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s63 0#u32 (0) (by scalar_tac) hinv63 h64 as ⟨v71, s64, hinv64, h_v71⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 h_v70 dropping
        store_step with Store.apply_mk_rep s64 v70 v71 _ _ hinv64 h64 h_v70 h_v71 as ⟨v72, s65, hinv65, h_v72⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 h_v64 dropping h_v70 h_v71 v70 v71
        store_step with Store.apply_mk_rep s65 v64 v72 _ _ hinv65 h64 h_v64 h_v72 as ⟨v73, s66, hinv66, h_v73⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v57 dropping h_v64 h_v72 v64 v72
        store_step with Store.apply_mk_rep s66 v57 v73 _ _ hinv66 h64 h_v57 h_v73 as ⟨v74, s67, hinv67, h_v74⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 dropping h_v57 h_v73 v57 v73
        try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
        store_step with Store.literal_int_u32_spec s67 1#u32 (1) (by scalar_tac) hinv67 h64 as ⟨v75, s68, hinv68, h_v75⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 h_v74 dropping
        store_step with Store.apply_mk_rep s68 v74 v75 _ _ hinv68 h64 h_v74 h_v75 as ⟨v76, s69, hinv69, h_v76⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 h_v56 dropping h_v74 h_v75 v74 v75
        store_step with Store.apply_mk_rep s69 v56 v76 _ _ hinv69 h64 h_v56 h_v76 as ⟨v77, s70, hinv70, h_v77⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 h_v54 dropping h_v56 h_v76 v56 v76
        store_step with Store.apply_mk_rep s70 v54 v77 _ _ hinv70 h64 h_v54 h_v77 as ⟨v78, s71, hinv71, h_v78⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v52 dropping h_v54 h_v77 v54 v77
        store_step with Store.apply_mk_rep s71 v52 v78 _ _ hinv71 h64 h_v52 h_v78 as ⟨v79, s72, hinv72, h_v79⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 dropping h_v52 h_v78 v52 v78
        store_step with Store.literal_boolean_spec s72 true hinv72 h64 as ⟨v80, s73, hinv73, h_v80⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 h_v79 dropping
        store_step with Store.apply_mk_rep s73 v79 v80 _ _ hinv73 h64 h_v79 h_v80 as ⟨v81, s74, hinv74, h_v81⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v51 dropping h_v79 h_v80 v79 v80
        store_step with Store.apply_mk_rep s74 v51 v81 _ _ hinv74 h64 h_v51 h_v81 as ⟨v82, s75, hinv75, h_v82⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v51 h_v81 v51 v81
        req_done hinv75 hG with h_v82 using hq_v33)
      store_step with h_req_v83 as ⟨v83, s76, hinv76, h_v83⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_req_v83 h_v33 h_v34 v33 v34
      ite_done hinv76 hG with (eo_ite_true_rep _ hx_32 h_v83)
    · ite_branch hbv_32
      step as ⟨e_v84, he_v84⟩
      store_step with CtorSpec.eo_and.construct s26 e_v84 (by rw [he_v84]; exact empty_args) hinv26 h64 as ⟨v84, s27, hinv27, h_v84⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v31 he_v84 e_v84 v31
      step as ⟨e_v85, he_v85⟩
      store_step with CtorSpec.eo__3d_3e.construct s27 e_v85 (by rw [he_v85]; exact empty_args) hinv27 h64 as ⟨v85, s28, hinv28, h_v85⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 dropping he_v85 e_v85
      step as ⟨e_v86, he_v86⟩
      store_step with CtorSpec.eo__3e.construct s28 e_v86 (by rw [he_v86]; exact empty_args) hinv28 h64 as ⟨v86, s29, hinv29, h_v86⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v85 dropping he_v86 e_v86
      store_step with Store.apply_rep s29 v86 v2 _ _ hinv29 h64 h_v86 h_v2 (by ns_tac) (by ns_tac) as ⟨v87, s30, hinv30, h_v87⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v85 dropping h_v86 v86
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s30 0#u32 (0) (by scalar_tac) hinv30 h64 as ⟨v88, s31, hinv31, h_v88⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v85 h_v87 dropping
      store_step with Store.apply_rep s31 v87 v88 _ _ hinv31 h64 h_v87 h_v88 (by ns_tac) (by ns_tac) as ⟨v89, s32, hinv32, h_v89⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v85 dropping h_v87 h_v88 v87 v88
      store_step with Store.apply_rep s32 v85 v89 _ _ hinv32 h64 h_v85 h_v89 (by ns_tac) (by ns_tac) as ⟨v90, s33, hinv33, h_v90⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 dropping h_v85 h_v89 hinv32 s32 v85 v89
      step as ⟨e_v91, he_v91⟩
      store_step with CtorSpec.eo_and.construct s33 e_v91 (by rw [he_v91]; exact empty_args) hinv33 h64 as ⟨v91, s34, hinv34, h_v91⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 dropping he_v91 hinv33 e_v91 s33
      step as ⟨e_v92, he_v92⟩
      store_step with CtorSpec.eo__3c_3d.construct s34 e_v92 (by rw [he_v92]; exact empty_args) hinv34 h64 as ⟨v92, s35, hinv35, h_v92⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 dropping he_v92 hinv34 e_v92 s34
      step as ⟨e_v93, he_v93⟩
      store_step with CtorSpec.eo__2a.construct s35 e_v93 (by rw [he_v93]; exact empty_args) hinv35 h64 as ⟨v93, s36, hinv36, h_v93⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 dropping he_v93 hinv35 e_v93 s35
      store_step with Store.apply_rep s36 v93 v2 _ _ hinv36 h64 h_v93 h_v2 (by ns_tac) (by ns_tac) as ⟨v94, s37, hinv37, h_v94⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 dropping h_v93 hinv36 s36 v93
      step as ⟨e_v95, he_v95⟩
      store_step with CtorSpec.eo__2a.construct s37 e_v95 (by rw [he_v95]; exact empty_args) hinv37 h64 as ⟨v95, s38, hinv38, h_v95⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 dropping he_v95 hinv37 e_v95 s37
      step as ⟨e_v96, he_v96⟩
      store_step with CtorSpec.eo__40purify.construct s38 e_v96 (by rw [he_v96]; exact empty_args) hinv38 h64 as ⟨v96, s39, hinv39, h_v96⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 h_v95 dropping he_v96 hinv38 e_v96 s38
      step as ⟨e_v97, he_v97⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s39 e_v97 (by rw [he_v97]; exact empty_args) hinv39 h64 as ⟨v97, s40, hinv40, h_v97⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 h_v95 h_v96 dropping he_v97 hinv39 e_v97 s39
      store_step with Store.apply_rep s40 v97 v5 _ _ hinv40 h64 h_v97 h_v5 (by ns_tac) (by ns_tac) as ⟨v98, s41, hinv41, h_v98⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 h_v95 h_v96 dropping h_v97 hinv40 s40 v97
      store_step with Store.apply_rep s41 v98 v2 _ _ hinv41 h64 h_v98 h_v2 (by ns_tac) (by ns_tac) as ⟨v99, s42, hinv42, h_v99⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 h_v95 h_v96 dropping h_v98 hinv41 s41 v98
      store_step with Store.apply_rep s42 v96 v99 _ _ hinv42 h64 h_v96 h_v99 (by ns_tac) (by ns_tac) as ⟨v100, s43, hinv43, h_v100⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 h_v95 dropping h_v96 h_v99 hinv42 s42 v96 v99
      store_step with Store.apply_rep s43 v95 v100 _ _ hinv43 h64 h_v95 h_v100 (by ns_tac) (by ns_tac) as ⟨v101, s44, hinv44, h_v101⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 dropping h_v100 h_v95 hinv43 s43 v100 v95
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s44 1#u32 (1) (by scalar_tac) hinv44 h64 as ⟨v102, s45, hinv45, h_v102⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 h_v101 dropping hinv44 s44
      store_step with Store.apply_rep s45 v101 v102 _ _ hinv45 h64 h_v101 h_v102 (by ns_tac) (by ns_tac) as ⟨v103, s46, hinv46, h_v103⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 h_v94 dropping h_v101 h_v102 hinv45 s45 v101 v102
      store_step with Store.apply_rep s46 v94 v103 _ _ hinv46 h64 h_v94 h_v103 (by ns_tac) (by ns_tac) as ⟨v104, s47, hinv47, h_v104⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 h_v92 dropping h_v103 h_v94 hinv46 s46 v103 v94
      store_step with Store.apply_rep s47 v92 v104 _ _ hinv47 h64 h_v92 h_v104 (by ns_tac) (by ns_tac) as ⟨v105, s48, hinv48, h_v105⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 dropping h_v104 h_v92 hinv47 s47 v104 v92
      store_step with Store.apply_rep s48 v105 v5 _ _ hinv48 h64 h_v105 h_v5 (by ns_tac) (by ns_tac) as ⟨v106, s49, hinv49, h_v106⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v91 dropping h_v105 hinv48 s48 v105
      store_step with Store.apply_rep s49 v91 v106 _ _ hinv49 h64 h_v91 h_v106 (by ns_tac) (by ns_tac) as ⟨v107, s50, hinv50, h_v107⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 dropping h_v106 h_v91 hinv49 s49 v106 v91
      step as ⟨e_v108, he_v108⟩
      store_step with CtorSpec.eo_and.construct s50 e_v108 (by rw [he_v108]; exact empty_args) hinv50 h64 as ⟨v108, s51, hinv51, h_v108⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 dropping he_v108 hinv50 e_v108 s50
      step as ⟨e_v109, he_v109⟩
      store_step with CtorSpec.eo__3c.construct s51 e_v109 (by rw [he_v109]; exact empty_args) hinv51 h64 as ⟨v109, s52, hinv52, h_v109⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 dropping he_v109 hinv51 e_v109 s51
      store_step with Store.apply_rep s52 v109 v5 _ _ hinv52 h64 h_v109 h_v5 (by ns_tac) (by ns_tac) as ⟨v110, s53, hinv53, h_v110⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 dropping h_v109 hinv52 s52 v109
      step as ⟨e_v111, he_v111⟩
      store_step with CtorSpec.eo__2a.construct s53 e_v111 (by rw [he_v111]; exact empty_args) hinv53 h64 as ⟨v111, s54, hinv54, h_v111⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 dropping he_v111 hinv53 e_v111 s53
      store_step with Store.apply_rep s54 v111 v2 _ _ hinv54 h64 h_v111 h_v2 (by ns_tac) (by ns_tac) as ⟨v112, s55, hinv55, h_v112⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 dropping h_v111 hinv54 s54 v111
      step as ⟨e_v113, he_v113⟩
      store_step with CtorSpec.eo__2a.construct s55 e_v113 (by rw [he_v113]; exact empty_args) hinv55 h64 as ⟨v113, s56, hinv56, h_v113⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 dropping he_v113 hinv55 e_v113 s55
      step as ⟨e_v114, he_v114⟩
      store_step with CtorSpec.eo__2b.construct s56 e_v114 (by rw [he_v114]; exact empty_args) hinv56 h64 as ⟨v114, s57, hinv57, h_v114⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 dropping he_v114 hinv56 e_v114 s56
      step as ⟨e_v115, he_v115⟩
      store_step with CtorSpec.eo__40purify.construct s57 e_v115 (by rw [he_v115]; exact empty_args) hinv57 h64 as ⟨v115, s58, hinv58, h_v115⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v114 dropping he_v115 hinv57 e_v115 s57
      step as ⟨e_v116, he_v116⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s58 e_v116 (by rw [he_v116]; exact empty_args) hinv58 h64 as ⟨v116, s59, hinv59, h_v116⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v114 h_v115 dropping he_v116 hinv58 e_v116 s58
      store_step with Store.apply_rep s59 v116 v5 _ _ hinv59 h64 h_v116 h_v5 (by ns_tac) (by ns_tac) as ⟨v117, s60, hinv60, h_v117⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v114 h_v115 dropping h_v116 hinv59 s59 v116
      store_step with Store.apply_rep s60 v117 v2 _ _ hinv60 h64 h_v117 h_v2 (by ns_tac) (by ns_tac) as ⟨v118, s61, hinv61, h_v118⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v114 h_v115 dropping h_v117 hinv60 s60 v117
      store_step with Store.apply_rep s61 v115 v118 _ _ hinv61 h64 h_v115 h_v118 (by ns_tac) (by ns_tac) as ⟨v119, s62, hinv62, h_v119⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v114 dropping h_v115 h_v118 hinv61 s61 v115 v118
      store_step with Store.apply_rep s62 v114 v119 _ _ hinv62 h64 h_v114 h_v119 (by ns_tac) (by ns_tac) as ⟨v120, s63, hinv63, h_v120⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 dropping h_v114 h_v119 hinv62 s62 v114 v119
      step as ⟨e_v121, he_v121⟩
      store_step with CtorSpec.eo__2b.construct s63 e_v121 (by rw [he_v121]; exact empty_args) hinv63 h64 as ⟨v121, s64, hinv64, h_v121⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v120 dropping he_v121 hinv63 e_v121 s63
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s64 1#u32 (1) (by scalar_tac) hinv64 h64 as ⟨v122, s65, hinv65, h_v122⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v120 h_v121 dropping hinv64 s64
      store_step with Store.apply_rep s65 v121 v122 _ _ hinv65 h64 h_v121 h_v122 (by ns_tac) (by ns_tac) as ⟨v123, s66, hinv66, h_v123⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v120 dropping h_v121 h_v122 hinv65 s65 v121 v122
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s66 0#u32 (0) (by scalar_tac) hinv66 h64 as ⟨v124, s67, hinv67, h_v124⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v120 h_v123 dropping hinv66 s66
      store_step with Store.apply_rep s67 v123 v124 _ _ hinv67 h64 h_v123 h_v124 (by ns_tac) (by ns_tac) as ⟨v125, s68, hinv68, h_v125⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 h_v120 dropping h_v123 h_v124 hinv67 s67 v123 v124
      store_step with Store.apply_rep s68 v120 v125 _ _ hinv68 h64 h_v120 h_v125 (by ns_tac) (by ns_tac) as ⟨v126, s69, hinv69, h_v126⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v113 dropping h_v120 h_v125 hinv68 s68 v120 v125
      store_step with Store.apply_rep s69 v113 v126 _ _ hinv69 h64 h_v113 h_v126 (by ns_tac) (by ns_tac) as ⟨v127, s70, hinv70, h_v127⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 dropping h_v113 h_v126 hinv69 s69 v113 v126
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s70 1#u32 (1) (by scalar_tac) hinv70 h64 as ⟨v128, s71, hinv71, h_v128⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 h_v127 dropping hinv70 s70
      store_step with Store.apply_rep s71 v127 v128 _ _ hinv71 h64 h_v127 h_v128 (by ns_tac) (by ns_tac) as ⟨v129, s72, hinv72, h_v129⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 h_v112 dropping h_v127 h_v128 hinv71 s71 v127 v128
      store_step with Store.apply_rep s72 v112 v129 _ _ hinv72 h64 h_v112 h_v129 (by ns_tac) (by ns_tac) as ⟨v130, s73, hinv73, h_v130⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 h_v110 dropping h_v112 h_v129 hinv72 s72 v112 v129
      store_step with Store.apply_rep s73 v110 v130 _ _ hinv73 h64 h_v110 h_v130 (by ns_tac) (by ns_tac) as ⟨v131, s74, hinv74, h_v131⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v108 dropping h_v110 h_v130 hinv73 s73 v110 v130
      store_step with Store.apply_rep s74 v108 v131 _ _ hinv74 h64 h_v108 h_v131 (by ns_tac) (by ns_tac) as ⟨v132, s75, hinv75, h_v132⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 dropping h_v108 h_v131 hinv74 s74 v108 v131
      store_step with Store.literal_boolean_spec s75 true hinv75 h64 as ⟨v133, s76, hinv76, h_v133⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 h_v132 dropping hinv75 s75
      store_step with Store.apply_rep s76 v132 v133 _ _ hinv76 h64 h_v132 h_v133 (by ns_tac) (by ns_tac) as ⟨v134, s77, hinv77, h_v134⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 h_v107 dropping h_v132 h_v133 hinv76 s76 v132 v133
      store_step with Store.apply_rep s77 v107 v134 _ _ hinv77 h64 h_v107 h_v134 (by ns_tac) (by ns_tac) as ⟨v135, s78, hinv78, h_v135⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 h_v90 dropping h_v107 h_v134 hinv77 s77 v107 v134
      store_step with Store.apply_rep s78 v90 v135 _ _ hinv78 h64 h_v90 h_v135 (by ns_tac) (by ns_tac) as ⟨v136, s79, hinv79, h_v136⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v84 dropping h_v135 h_v90 hinv78 s78 v135 v90
      store_step with Store.apply_rep s79 v84 v136 _ _ hinv79 h64 h_v84 h_v136 (by ns_tac) (by ns_tac) as ⟨v137, s80, hinv80, h_v137⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 dropping h_v136 h_v84 hinv79 s79 v136 v84
      step as ⟨e_v138, he_v138⟩
      store_step with CtorSpec.eo_and.construct s80 e_v138 (by rw [he_v138]; exact empty_args) hinv80 h64 as ⟨v138, s81, hinv81, h_v138⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 dropping he_v138 hinv80 e_v138 s80
      step as ⟨e_v139, he_v139⟩
      store_step with CtorSpec.eo__3d_3e.construct s81 e_v139 (by rw [he_v139]; exact empty_args) hinv81 h64 as ⟨v139, s82, hinv82, h_v139⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 dropping he_v139 hinv81 e_v139 s81
      step as ⟨e_v140, he_v140⟩
      store_step with CtorSpec.eo__3c.construct s82 e_v140 (by rw [he_v140]; exact empty_args) hinv82 h64 as ⟨v140, s83, hinv83, h_v140⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v139 dropping he_v140 hinv82 e_v140 s82
      store_step with Store.apply_rep s83 v140 v2 _ _ hinv83 h64 h_v140 h_v2 (by ns_tac) (by ns_tac) as ⟨v141, s84, hinv84, h_v141⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v139 dropping h_v140 hinv83 s83 v140
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s84 0#u32 (0) (by scalar_tac) hinv84 h64 as ⟨v142, s85, hinv85, h_v142⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v139 h_v141 dropping hinv84 s84
      store_step with Store.apply_rep s85 v141 v142 _ _ hinv85 h64 h_v141 h_v142 (by ns_tac) (by ns_tac) as ⟨v143, s86, hinv86, h_v143⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v139 dropping h_v141 h_v142 hinv85 s85 v141 v142
      store_step with Store.apply_rep s86 v139 v143 _ _ hinv86 h64 h_v139 h_v143 (by ns_tac) (by ns_tac) as ⟨v144, s87, hinv87, h_v144⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 dropping h_v139 h_v143 hinv86 s86 v139 v143
      step as ⟨e_v145, he_v145⟩
      store_step with CtorSpec.eo_and.construct s87 e_v145 (by rw [he_v145]; exact empty_args) hinv87 h64 as ⟨v145, s88, hinv88, h_v145⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 dropping he_v145 hinv87 e_v145 s87
      step as ⟨e_v146, he_v146⟩
      store_step with CtorSpec.eo__3c_3d.construct s88 e_v146 (by rw [he_v146]; exact empty_args) hinv88 h64 as ⟨v146, s89, hinv89, h_v146⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 dropping he_v146 hinv88 e_v146 s88
      step as ⟨e_v147, he_v147⟩
      store_step with CtorSpec.eo__2a.construct s89 e_v147 (by rw [he_v147]; exact empty_args) hinv89 h64 as ⟨v147, s90, hinv90, h_v147⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 dropping he_v147 hinv89 e_v147 s89
      store_step with Store.apply_rep s90 v147 v2 _ _ hinv90 h64 h_v147 h_v2 (by ns_tac) (by ns_tac) as ⟨v148, s91, hinv91, h_v148⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 dropping h_v147 hinv90 s90 v147
      step as ⟨e_v149, he_v149⟩
      store_step with CtorSpec.eo__2a.construct s91 e_v149 (by rw [he_v149]; exact empty_args) hinv91 h64 as ⟨v149, s92, hinv92, h_v149⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 dropping he_v149 hinv91 e_v149 s91
      step as ⟨e_v150, he_v150⟩
      store_step with CtorSpec.eo__40purify.construct s92 e_v150 (by rw [he_v150]; exact empty_args) hinv92 h64 as ⟨v150, s93, hinv93, h_v150⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 h_v149 dropping he_v150 hinv92 e_v150 s92
      step as ⟨e_v151, he_v151⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s93 e_v151 (by rw [he_v151]; exact empty_args) hinv93 h64 as ⟨v151, s94, hinv94, h_v151⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 h_v149 h_v150 dropping he_v151 hinv93 e_v151 s93
      store_step with Store.apply_rep s94 v151 v5 _ _ hinv94 h64 h_v151 h_v5 (by ns_tac) (by ns_tac) as ⟨v152, s95, hinv95, h_v152⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 h_v149 h_v150 dropping h_v151 hinv94 s94 v151
      store_step with Store.apply_rep s95 v152 v2 _ _ hinv95 h64 h_v152 h_v2 (by ns_tac) (by ns_tac) as ⟨v153, s96, hinv96, h_v153⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 h_v149 h_v150 dropping h_v152 hinv95 s95 v152
      store_step with Store.apply_rep s96 v150 v153 _ _ hinv96 h64 h_v150 h_v153 (by ns_tac) (by ns_tac) as ⟨v154, s97, hinv97, h_v154⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 h_v149 dropping h_v150 h_v153 hinv96 s96 v150 v153
      store_step with Store.apply_rep s97 v149 v154 _ _ hinv97 h64 h_v149 h_v154 (by ns_tac) (by ns_tac) as ⟨v155, s98, hinv98, h_v155⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 dropping h_v149 h_v154 hinv97 s97 v149 v154
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s98 1#u32 (1) (by scalar_tac) hinv98 h64 as ⟨v156, s99, hinv99, h_v156⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 h_v155 dropping hinv98 s98
      store_step with Store.apply_rep s99 v155 v156 _ _ hinv99 h64 h_v155 h_v156 (by ns_tac) (by ns_tac) as ⟨v157, s100, hinv100, h_v157⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 h_v148 dropping h_v155 h_v156 hinv99 s99 v155 v156
      store_step with Store.apply_rep s100 v148 v157 _ _ hinv100 h64 h_v148 h_v157 (by ns_tac) (by ns_tac) as ⟨v158, s101, hinv101, h_v158⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 h_v146 dropping h_v148 h_v157 hinv100 s100 v148 v157
      store_step with Store.apply_rep s101 v146 v158 _ _ hinv101 h64 h_v146 h_v158 (by ns_tac) (by ns_tac) as ⟨v159, s102, hinv102, h_v159⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 dropping h_v146 h_v158 hinv101 s101 v146 v158
      store_step with Store.apply_rep s102 v159 v5 _ _ hinv102 h64 h_v159 h_v5 (by ns_tac) (by ns_tac) as ⟨v160, s103, hinv103, h_v160⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v145 dropping h_v159 hinv102 s102 v159
      store_step with Store.apply_rep s103 v145 v160 _ _ hinv103 h64 h_v145 h_v160 (by ns_tac) (by ns_tac) as ⟨v161, s104, hinv104, h_v161⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 dropping h_v145 h_v160 hinv103 s103 v145 v160
      step as ⟨e_v162, he_v162⟩
      store_step with CtorSpec.eo_and.construct s104 e_v162 (by rw [he_v162]; exact empty_args) hinv104 h64 as ⟨v162, s105, hinv105, h_v162⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 dropping he_v162 hinv104 e_v162 s104
      step as ⟨e_v163, he_v163⟩
      store_step with CtorSpec.eo__3c.construct s105 e_v163 (by rw [he_v163]; exact empty_args) hinv105 h64 as ⟨v163, s106, hinv106, h_v163⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 dropping he_v163 hinv105 e_v163 s105
      store_step with Store.apply_rep s106 v163 v5 _ _ hinv106 h64 h_v163 h_v5 (by ns_tac) (by ns_tac) as ⟨v164, s107, hinv107, h_v164⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 dropping h_v163 hinv106 s106 v163
      step as ⟨e_v165, he_v165⟩
      store_step with CtorSpec.eo__2a.construct s107 e_v165 (by rw [he_v165]; exact empty_args) hinv107 h64 as ⟨v165, s108, hinv108, h_v165⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 dropping he_v165 hinv107 e_v165 s107
      store_step with Store.apply_rep s108 v165 v2 _ _ hinv108 h64 h_v165 h_v2 (by ns_tac) (by ns_tac) as ⟨v166, s109, hinv109, h_v166⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 dropping h_v165 hinv108 s108 v165
      step as ⟨e_v167, he_v167⟩
      store_step with CtorSpec.eo__2a.construct s109 e_v167 (by rw [he_v167]; exact empty_args) hinv109 h64 as ⟨v167, s110, hinv110, h_v167⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 dropping he_v167 hinv109 e_v167 s109
      step as ⟨e_v168, he_v168⟩
      store_step with CtorSpec.eo__2b.construct s110 e_v168 (by rw [he_v168]; exact empty_args) hinv110 h64 as ⟨v168, s111, hinv111, h_v168⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 dropping he_v168 hinv110 e_v168 s110
      step as ⟨e_v169, he_v169⟩
      store_step with CtorSpec.eo__40purify.construct s111 e_v169 (by rw [he_v169]; exact empty_args) hinv111 h64 as ⟨v169, s112, hinv112, h_v169⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v168 dropping he_v169 hinv111 e_v169 s111
      step as ⟨e_v170, he_v170⟩
      store_step with CtorSpec.eo_div_5ftotal.construct s112 e_v170 (by rw [he_v170]; exact empty_args) hinv112 h64 as ⟨v170, s113, hinv113, h_v170⟩ growing hG carrying h_v2 h_v5 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v168 h_v169 dropping he_v170 hinv112 e_v170 s112
      store_step with Store.apply_rep s113 v170 v5 _ _ hinv113 h64 h_v170 h_v5 (by ns_tac) (by ns_tac) as ⟨v171, s114, hinv114, h_v171⟩ growing hG carrying h_v2 h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v168 h_v169 dropping h_v170 h_v5 hinv113 s113 v170 v5
      store_step with Store.apply_rep s114 v171 v2 _ _ hinv114 h64 h_v171 h_v2 (by ns_tac) (by ns_tac) as ⟨v172, s115, hinv115, h_v172⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v168 h_v169 dropping h_v171 h_v2 hinv114 s114 v171 v2
      store_step with Store.apply_rep s115 v169 v172 _ _ hinv115 h64 h_v169 h_v172 (by ns_tac) (by ns_tac) as ⟨v173, s116, hinv116, h_v173⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v168 dropping h_v169 h_v172 hinv115 s115 v169 v172
      store_step with Store.apply_rep s116 v168 v173 _ _ hinv116 h64 h_v168 h_v173 (by ns_tac) (by ns_tac) as ⟨v174, s117, hinv117, h_v174⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 dropping h_v168 h_v173 hinv116 s116 v168 v173
      step as ⟨e_v175, he_v175⟩
      store_step with CtorSpec.eo__2b.construct s117 e_v175 (by rw [he_v175]; exact empty_args) hinv117 h64 as ⟨v175, s118, hinv118, h_v175⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v174 dropping he_v175 hinv117 e_v175 s117
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_neg_u32_spec s118 1#u32 (-1) (by scalar_tac) hinv118 h64 as ⟨v176, s119, hinv119, h_v176⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v174 h_v175 dropping hinv118 s118
      store_step with Store.apply_rep s119 v175 v176 _ _ hinv119 h64 h_v175 h_v176 (by ns_tac) (by ns_tac) as ⟨v177, s120, hinv120, h_v177⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v174 dropping h_v175 h_v176 hinv119 s119 v175 v176
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s120 0#u32 (0) (by scalar_tac) hinv120 h64 as ⟨v178, s121, hinv121, h_v178⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v174 h_v177 dropping hinv120 s120
      store_step with Store.apply_rep s121 v177 v178 _ _ hinv121 h64 h_v177 h_v178 (by ns_tac) (by ns_tac) as ⟨v179, s122, hinv122, h_v179⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 h_v174 dropping h_v177 h_v178 hinv121 s121 v177 v178
      store_step with Store.apply_rep s122 v174 v179 _ _ hinv122 h64 h_v174 h_v179 (by ns_tac) (by ns_tac) as ⟨v180, s123, hinv123, h_v180⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v167 dropping h_v174 h_v179 hinv122 s122 v174 v179
      store_step with Store.apply_rep s123 v167 v180 _ _ hinv123 h64 h_v167 h_v180 (by ns_tac) (by ns_tac) as ⟨v181, s124, hinv124, h_v181⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 dropping h_v167 h_v180 hinv123 s123 v167 v180
      try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      store_step with Store.literal_int_u32_spec s124 1#u32 (1) (by scalar_tac) hinv124 h64 as ⟨v182, s125, hinv125, h_v182⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 h_v181 dropping hinv124 s124
      store_step with Store.apply_rep s125 v181 v182 _ _ hinv125 h64 h_v181 h_v182 (by ns_tac) (by ns_tac) as ⟨v183, s126, hinv126, h_v183⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 h_v166 dropping h_v181 h_v182 hinv125 s125 v181 v182
      store_step with Store.apply_rep s126 v166 v183 _ _ hinv126 h64 h_v166 h_v183 (by ns_tac) (by ns_tac) as ⟨v184, s127, hinv127, h_v184⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 h_v164 dropping h_v166 h_v183 hinv126 s126 v166 v183
      store_step with Store.apply_rep s127 v164 v184 _ _ hinv127 h64 h_v164 h_v184 (by ns_tac) (by ns_tac) as ⟨v185, s128, hinv128, h_v185⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v162 dropping h_v164 h_v184 hinv127 s127 v164 v184
      store_step with Store.apply_rep s128 v162 v185 _ _ hinv128 h64 h_v162 h_v185 (by ns_tac) (by ns_tac) as ⟨v186, s129, hinv129, h_v186⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 dropping h_v162 h_v185 hinv128 s128 v162 v185
      store_step with Store.literal_boolean_spec s129 true hinv129 h64 as ⟨v187, s130, hinv130, h_v187⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 h_v186 dropping hinv129 s129
      store_step with Store.apply_rep s130 v186 v187 _ _ hinv130 h64 h_v186 h_v187 (by ns_tac) (by ns_tac) as ⟨v188, s131, hinv131, h_v188⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 h_v161 dropping h_v186 h_v187 hinv130 s130 v186 v187
      store_step with Store.apply_rep s131 v161 v188 _ _ hinv131 h64 h_v161 h_v188 (by ns_tac) (by ns_tac) as ⟨v189, s132, hinv132, h_v189⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 h_v144 dropping h_v161 h_v188 hinv131 s131 v161 v188
      store_step with Store.apply_rep s132 v144 v189 _ _ hinv132 h64 h_v144 h_v189 (by ns_tac) (by ns_tac) as ⟨v190, s133, hinv133, h_v190⟩ growing hG carrying h_v29 h_v30 h_v137 h_v138 dropping h_v144 h_v189 hinv132 s132 v144 v189
      store_step with Store.apply_rep s133 v138 v190 _ _ hinv133 h64 h_v138 h_v190 (by ns_tac) (by ns_tac) as ⟨v191, s134, hinv134, h_v191⟩ growing hG carrying h_v29 h_v30 h_v137 dropping h_v138 h_v190 hinv133 s133 v138 v190
      store_step with Store.literal_boolean_spec s134 true hinv134 h64 as ⟨v192, s135, hinv135, h_v192⟩ growing hG carrying h_v29 h_v30 h_v137 h_v191 dropping hinv134 s134
      store_step with Store.apply_rep s135 v191 v192 _ _ hinv135 h64 h_v191 h_v192 (by ns_tac) (by ns_tac) as ⟨v193, s136, hinv136, h_v193⟩ growing hG carrying h_v29 h_v30 h_v137 dropping h_v191 h_v192 hinv135 s135 v191 v192
      store_step with Store.apply_rep s136 v137 v193 _ _ hinv136 h64 h_v137 h_v193 (by ns_tac) (by ns_tac) as ⟨v194, s137, hinv137, h_v194⟩ growing hG carrying h_v29 h_v30 dropping h_v137 h_v193 hinv136 s136 v137 v193
      ite_done hinv137 hG with (eo_ite_false_rep _ hx_32 h_v194)
    · ite_branch hbv_32
      ite_stuck hinv26 hG with hx_32)
  store_step with h_ite_v195 as ⟨v195, s27, hinv27, h_v195⟩ growing hG carrying h_v29 h_v30 dropping h_ite_v195 h_v2 h_v31 h_v5 hinv26 s26 v2 v31 v5
  store_step with Store.apply_mk_rep s27 v30 v195 _ _ hinv27 h64 h_v30 h_v195 as ⟨v196, s28, hinv28, h_v196⟩ growing hG carrying h_v29 dropping h_v195 h_v30 hinv27 s27 v195 v30
  store_step with Store.literal_boolean_spec s28 true hinv28 h64 as ⟨v197, s29, hinv29, h_v197⟩ growing hG carrying h_v29 h_v196 dropping hinv28 s28
  store_step with Store.apply_mk_rep s29 v196 v197 _ _ hinv29 h64 h_v196 h_v197 as ⟨v198, s30, hinv30, h_v198⟩ growing hG carrying h_v29 dropping h_v196 h_v197 hinv29 s29 v196 v197
  store_step with Store.apply_mk_rep s30 v29 v198 _ _ hinv30 h64 h_v29 h_v198 as ⟨v199, s31, hinv31, h_v199⟩ growing hG carrying dropping h_v198 h_v29 hinv30 s30 v198 v29
  case_done hinv31 hG with h_v199 in EoCases.__arith_reduction_pred.case_7 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_8_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_8_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_8 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_8 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_8
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_abs.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_8
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo_abs.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  store_step with Store.apply_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 (by ns_tac) (by ns_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 dropping h_v5 hinv3 s3 v5
  store_step with Store.apply_rep s4 v4 v6 _ _ hinv4 h64 h_v4 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 dropping h_v4 h_v6 hinv4 s4 v4 v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s5 e_v8 (by rw [he_v8]; exact empty_args) hinv5 h64 as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v7 dropping he_v8 hinv5 e_v8 s5
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3c.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v7 h_v8 dropping he_v9 hinv6 e_v9 s6
  store_step with Store.apply_rep s7 v9 v2 _ _ hinv7 h64 h_v9 h_v2 (by ns_tac) (by ns_tac) as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v7 h_v8 dropping h_v9 hinv7 s7 v9
  store_step with ih.eo__24eo_5ftypeof s8 v2 _ hinv8 h64 (hG.rem hrem) h_v2 as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v7 h_v8 h_v10 dropping hinv8 s8
  store_step with ih.eo__24arith_5fmk_5fzero s9 v11 _ hinv9 h64 (hG.rem hrem) h_v11 as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v7 h_v8 h_v10 dropping h_v11 hinv9 s9 v11
  store_step with Store.apply_mk_rep s10 v10 v12 _ _ hinv10 h64 h_v10 h_v12 as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v7 h_v8 dropping h_v10 h_v12 hinv10 s10 v10 v12
  store_step with Store.apply_mk_rep s11 v8 v13 _ _ hinv11 h64 h_v8 h_v13 as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 h_v7 dropping h_v13 h_v8 hinv11 s11 v13 v8
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__24eoo_5f_2d_2e2.construct s12 e_v15 (by rw [he_v15]; exact empty_args) hinv12 h64 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v7 h_v14 dropping he_v15 hinv12 e_v15 s12
  store_step with Store.apply_rep s13 v15 v2 _ _ hinv13 h64 h_v15 h_v2 (by ns_tac) (by ns_tac) as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 h_v7 h_v14 dropping h_v15 hinv13 s13 v15
  store_step with Store.apply_mk_rep s14 v14 v16 _ _ hinv14 h64 h_v14 h_v16 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v7 dropping h_v14 h_v16 hinv14 s14 v14 v16
  store_step with Store.apply_mk_rep s15 v17 v2 _ _ hinv15 h64 h_v17 h_v2 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v7 dropping h_v17 h_v2 hinv15 s15 v17 v2
  store_step with Store.apply_mk_rep s16 v7 v18 _ _ hinv16 h64 h_v7 h_v18 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying dropping h_v18 h_v7 hinv16 s16 v18 v7
  case_done hinv17 hG with h_v19 in EoCases.__arith_reduction_pred.case_8 using hn_a0 hn_v1 hn_v2

set_option maxHeartbeats 2430000 in
theorem case_9_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_9_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_reduction_pred.case_9 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__arith_reduction_pred.case_9
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_int_2elog2.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_v1 h_v2 dropping h_a0 he_v3 e_v3
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_reduction_pred.case_9
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_and.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_v2 dropping h_v1 h_v3 he_v4 hinv1 e_v4 s1 v1 v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_v2 h_v4 dropping he_v5 hinv2 e_v5 s2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_int_2elog2.construct s3 e_v6 (by rw [he_v6]; exact empty_args) hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5 dropping he_v6 hinv3 e_v6 s3
  store_step with Store.apply_rep s4 v6 v2 _ _ hinv4 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_v2 h_v4 h_v5 dropping h_v6 hinv4 s4 v6
  store_step with Store.apply_rep s5 v5 v7 _ _ hinv5 h64 h_v5 h_v7 (by ns_tac) (by ns_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_v2 h_v4 dropping h_v5 h_v7 hinv5 s5 v5 v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__40purify.construct s6 e_v9 (by rw [he_v9]; exact empty_args) hinv6 h64 as ⟨v9, s7, hinv7, h_v9⟩ growing hG carrying h_v2 h_v4 h_v8 dropping he_v9 hinv6 e_v9 s6
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_int_2elog2.construct s7 e_v10 (by rw [he_v10]; exact empty_args) hinv7 h64 as ⟨v10, s8, hinv8, h_v10⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping he_v10 hinv7 e_v10 s7
  store_step with Store.apply_rep s8 v10 v2 _ _ hinv8 h64 h_v10 h_v2 (by ns_tac) (by ns_tac) as ⟨v11, s9, hinv9, h_v11⟩ growing hG carrying h_v2 h_v4 h_v8 h_v9 dropping h_v10 hinv8 s8 v10
  store_step with Store.apply_rep s9 v9 v11 _ _ hinv9 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s10, hinv10, h_v12⟩ growing hG carrying h_v2 h_v4 h_v8 dropping h_v11 h_v9 hinv9 s9 v11 v9
  store_step with Store.apply_rep s10 v8 v12 _ _ hinv10 h64 h_v8 h_v12 (by ns_tac) (by ns_tac) as ⟨v13, s11, hinv11, h_v13⟩ growing hG carrying h_v2 h_v4 dropping h_v12 h_v8 hinv10 s10 v12 v8
  store_step with Store.apply_rep s11 v4 v13 _ _ hinv11 h64 h_v4 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s12, hinv12, h_v14⟩ growing hG carrying h_v2 dropping h_v13 h_v4 hinv11 s11 v13 v4
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_and.construct s12 e_v15 (by rw [he_v15]; exact empty_args) hinv12 h64 as ⟨v15, s13, hinv13, h_v15⟩ growing hG carrying h_v2 h_v14 dropping he_v15 hinv12 e_v15 s12
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo_and.construct s13 e_v16 (by rw [he_v16]; exact empty_args) hinv13 h64 as ⟨v16, s14, hinv14, h_v16⟩ growing hG carrying h_v2 h_v14 h_v15 dropping he_v16 hinv13 e_v16 s13
  step as ⟨e_v17, he_v17⟩
  store_step with CtorSpec.eo__3d_3e.construct s14 e_v17 (by rw [he_v17]; exact empty_args) hinv14 h64 as ⟨v17, s15, hinv15, h_v17⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 dropping he_v17 hinv14 e_v17 s14
  step as ⟨e_v18, he_v18⟩
  store_step with CtorSpec.eo__3c.construct s15 e_v18 (by rw [he_v18]; exact empty_args) hinv15 h64 as ⟨v18, s16, hinv16, h_v18⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v17 dropping he_v18 hinv15 e_v18 s15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s16 0#u32 (0) (by scalar_tac) hinv16 h64 as ⟨v19, s17, hinv17, h_v19⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v17 h_v18 dropping hinv16 s16
  store_step with Store.apply_rep s17 v18 v19 _ _ hinv17 h64 h_v18 h_v19 (by ns_tac) (by ns_tac) as ⟨v20, s18, hinv18, h_v20⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v17 dropping h_v18 h_v19 hinv17 s17 v18 v19
  store_step with Store.apply_rep s18 v20 v2 _ _ hinv18 h64 h_v20 h_v2 (by ns_tac) (by ns_tac) as ⟨v21, s19, hinv19, h_v21⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v17 dropping h_v20 hinv18 s18 v20
  store_step with Store.apply_rep s19 v17 v21 _ _ hinv19 h64 h_v17 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s20, hinv20, h_v22⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 dropping h_v17 h_v21 hinv19 s19 v17 v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_and.construct s20 e_v23 (by rw [he_v23]; exact empty_args) hinv20 h64 as ⟨v23, s21, hinv21, h_v23⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 dropping he_v23 hinv20 e_v23 s20
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo__3c_3d.construct s21 e_v24 (by rw [he_v24]; exact empty_args) hinv21 h64 as ⟨v24, s22, hinv22, h_v24⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 dropping he_v24 hinv21 e_v24 s21
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_int_2epow2.construct s22 e_v25 (by rw [he_v25]; exact empty_args) hinv22 h64 as ⟨v25, s23, hinv23, h_v25⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 h_v24 dropping he_v25 hinv22 e_v25 s22
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo__40purify.construct s23 e_v26 (by rw [he_v26]; exact empty_args) hinv23 h64 as ⟨v26, s24, hinv24, h_v26⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 h_v24 h_v25 dropping he_v26 hinv23 e_v26 s23
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_int_2elog2.construct s24 e_v27 (by rw [he_v27]; exact empty_args) hinv24 h64 as ⟨v27, s25, hinv25, h_v27⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 h_v24 h_v25 h_v26 dropping he_v27 hinv24 e_v27 s24
  store_step with Store.apply_rep s25 v27 v2 _ _ hinv25 h64 h_v27 h_v2 (by ns_tac) (by ns_tac) as ⟨v28, s26, hinv26, h_v28⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 h_v24 h_v25 h_v26 dropping h_v27 hinv25 s25 v27
  store_step with Store.apply_rep s26 v26 v28 _ _ hinv26 h64 h_v26 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s27, hinv27, h_v29⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 h_v24 h_v25 dropping h_v26 h_v28 hinv26 s26 v26 v28
  store_step with Store.apply_rep s27 v25 v29 _ _ hinv27 h64 h_v25 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s28, hinv28, h_v30⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 h_v24 dropping h_v25 h_v29 hinv27 s27 v25 v29
  store_step with Store.apply_rep s28 v24 v30 _ _ hinv28 h64 h_v24 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s29, hinv29, h_v31⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 dropping h_v24 h_v30 hinv28 s28 v24 v30
  store_step with Store.apply_rep s29 v31 v2 _ _ hinv29 h64 h_v31 h_v2 (by ns_tac) (by ns_tac) as ⟨v32, s30, hinv30, h_v32⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v23 dropping h_v31 hinv29 s29 v31
  store_step with Store.apply_rep s30 v23 v32 _ _ hinv30 h64 h_v23 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s31, hinv31, h_v33⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 dropping h_v23 h_v32 hinv30 s30 v23 v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_and.construct s31 e_v34 (by rw [he_v34]; exact empty_args) hinv31 h64 as ⟨v34, s32, hinv32, h_v34⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 dropping he_v34 hinv31 e_v34 s31
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo__3c.construct s32 e_v35 (by rw [he_v35]; exact empty_args) hinv32 h64 as ⟨v35, s33, hinv33, h_v35⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 dropping he_v35 hinv32 e_v35 s32
  store_step with Store.apply_rep s33 v35 v2 _ _ hinv33 h64 h_v35 h_v2 (by ns_tac) (by ns_tac) as ⟨v36, s34, hinv34, h_v36⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 dropping h_v35 hinv33 s33 v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_int_2epow2.construct s34 e_v37 (by rw [he_v37]; exact empty_args) hinv34 h64 as ⟨v37, s35, hinv35, h_v37⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 dropping he_v37 hinv34 e_v37 s34
  step as ⟨e_v38, he_v38⟩
  store_step with CtorSpec.eo__2b.construct s35 e_v38 (by rw [he_v38]; exact empty_args) hinv35 h64 as ⟨v38, s36, hinv36, h_v38⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 dropping he_v38 hinv35 e_v38 s35
  step as ⟨e_v39, he_v39⟩
  store_step with CtorSpec.eo__40purify.construct s36 e_v39 (by rw [he_v39]; exact empty_args) hinv36 h64 as ⟨v39, s37, hinv37, h_v39⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v38 dropping he_v39 hinv36 e_v39 s36
  step as ⟨e_v40, he_v40⟩
  store_step with CtorSpec.eo_int_2elog2.construct s37 e_v40 (by rw [he_v40]; exact empty_args) hinv37 h64 as ⟨v40, s38, hinv38, h_v40⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v38 h_v39 dropping he_v40 hinv37 e_v40 s37
  store_step with Store.apply_rep s38 v40 v2 _ _ hinv38 h64 h_v40 h_v2 (by ns_tac) (by ns_tac) as ⟨v41, s39, hinv39, h_v41⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v38 h_v39 dropping h_v40 hinv38 s38 v40
  store_step with Store.apply_rep s39 v39 v41 _ _ hinv39 h64 h_v39 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s40, hinv40, h_v42⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v38 dropping h_v39 h_v41 hinv39 s39 v39 v41
  store_step with Store.apply_rep s40 v38 v42 _ _ hinv40 h64 h_v38 h_v42 (by ns_tac) (by ns_tac) as ⟨v43, s41, hinv41, h_v43⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 dropping h_v38 h_v42 hinv40 s40 v38 v42
  step as ⟨e_v44, he_v44⟩
  store_step with CtorSpec.eo__2b.construct s41 e_v44 (by rw [he_v44]; exact empty_args) hinv41 h64 as ⟨v44, s42, hinv42, h_v44⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v43 dropping he_v44 hinv41 e_v44 s41
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s42 1#u32 (1) (by scalar_tac) hinv42 h64 as ⟨v45, s43, hinv43, h_v45⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v43 h_v44 dropping hinv42 s42
  store_step with Store.apply_rep s43 v44 v45 _ _ hinv43 h64 h_v44 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s44, hinv44, h_v46⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v43 dropping h_v44 h_v45 hinv43 s43 v44 v45
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s44 0#u32 (0) (by scalar_tac) hinv44 h64 as ⟨v47, s45, hinv45, h_v47⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v43 h_v46 dropping hinv44 s44
  store_step with Store.apply_rep s45 v46 v47 _ _ hinv45 h64 h_v46 h_v47 (by ns_tac) (by ns_tac) as ⟨v48, s46, hinv46, h_v48⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 h_v43 dropping h_v46 h_v47 hinv45 s45 v46 v47
  store_step with Store.apply_rep s46 v43 v48 _ _ hinv46 h64 h_v43 h_v48 (by ns_tac) (by ns_tac) as ⟨v49, s47, hinv47, h_v49⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 h_v37 dropping h_v43 h_v48 hinv46 s46 v43 v48
  store_step with Store.apply_rep s47 v37 v49 _ _ hinv47 h64 h_v37 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s48, hinv48, h_v50⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 h_v36 dropping h_v37 h_v49 hinv47 s47 v37 v49
  store_step with Store.apply_rep s48 v36 v50 _ _ hinv48 h64 h_v36 h_v50 (by ns_tac) (by ns_tac) as ⟨v51, s49, hinv49, h_v51⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v34 dropping h_v36 h_v50 hinv48 s48 v36 v50
  store_step with Store.apply_rep s49 v34 v51 _ _ hinv49 h64 h_v34 h_v51 (by ns_tac) (by ns_tac) as ⟨v52, s50, hinv50, h_v52⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 dropping h_v34 h_v51 hinv49 s49 v34 v51
  store_step with Store.literal_boolean_spec s50 true hinv50 h64 as ⟨v53, s51, hinv51, h_v53⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 h_v52 dropping hinv50 s50
  store_step with Store.apply_rep s51 v52 v53 _ _ hinv51 h64 h_v52 h_v53 (by ns_tac) (by ns_tac) as ⟨v54, s52, hinv52, h_v54⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 h_v33 dropping h_v52 h_v53 hinv51 s51 v52 v53
  store_step with Store.apply_rep s52 v33 v54 _ _ hinv52 h64 h_v33 h_v54 (by ns_tac) (by ns_tac) as ⟨v55, s53, hinv53, h_v55⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 h_v22 dropping h_v33 h_v54 hinv52 s52 v33 v54
  store_step with Store.apply_rep s53 v22 v55 _ _ hinv53 h64 h_v22 h_v55 (by ns_tac) (by ns_tac) as ⟨v56, s54, hinv54, h_v56⟩ growing hG carrying h_v2 h_v14 h_v15 h_v16 dropping h_v22 h_v55 hinv53 s53 v22 v55
  store_step with Store.apply_rep s54 v16 v56 _ _ hinv54 h64 h_v16 h_v56 (by ns_tac) (by ns_tac) as ⟨v57, s55, hinv55, h_v57⟩ growing hG carrying h_v2 h_v14 h_v15 dropping h_v16 h_v56 hinv54 s54 v16 v56
  step as ⟨e_v58, he_v58⟩
  store_step with CtorSpec.eo_and.construct s55 e_v58 (by rw [he_v58]; exact empty_args) hinv55 h64 as ⟨v58, s56, hinv56, h_v58⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 dropping he_v58 hinv55 e_v58 s55
  step as ⟨e_v59, he_v59⟩
  store_step with CtorSpec.eo__3d_3e.construct s56 e_v59 (by rw [he_v59]; exact empty_args) hinv56 h64 as ⟨v59, s57, hinv57, h_v59⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 dropping he_v59 hinv56 e_v59 s56
  step as ⟨e_v60, he_v60⟩
  store_step with CtorSpec.eo_not.construct s57 e_v60 (by rw [he_v60]; exact empty_args) hinv57 h64 as ⟨v60, s58, hinv58, h_v60⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v59 dropping he_v60 hinv57 e_v60 s57
  step as ⟨e_v61, he_v61⟩
  store_step with CtorSpec.eo__3c.construct s58 e_v61 (by rw [he_v61]; exact empty_args) hinv58 h64 as ⟨v61, s59, hinv59, h_v61⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v59 h_v60 dropping he_v61 hinv58 e_v61 s58
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s59 0#u32 (0) (by scalar_tac) hinv59 h64 as ⟨v62, s60, hinv60, h_v62⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v59 h_v60 h_v61 dropping hinv59 s59
  store_step with Store.apply_rep s60 v61 v62 _ _ hinv60 h64 h_v61 h_v62 (by ns_tac) (by ns_tac) as ⟨v63, s61, hinv61, h_v63⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v59 h_v60 dropping h_v61 h_v62 hinv60 s60 v61 v62
  store_step with Store.apply_rep s61 v63 v2 _ _ hinv61 h64 h_v63 h_v2 (by ns_tac) (by ns_tac) as ⟨v64, s62, hinv62, h_v64⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v59 h_v60 dropping h_v63 hinv61 s61 v63
  store_step with Store.apply_rep s62 v60 v64 _ _ hinv62 h64 h_v60 h_v64 (by ns_tac) (by ns_tac) as ⟨v65, s63, hinv63, h_v65⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v59 dropping h_v60 h_v64 hinv62 s62 v60 v64
  store_step with Store.apply_rep s63 v59 v65 _ _ hinv63 h64 h_v59 h_v65 (by ns_tac) (by ns_tac) as ⟨v66, s64, hinv64, h_v66⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 dropping h_v59 h_v65 hinv63 s63 v59 v65
  step as ⟨e_v67, he_v67⟩
  store_step with CtorSpec.eo__3d.construct s64 e_v67 (by rw [he_v67]; exact empty_args) hinv64 h64 as ⟨v67, s65, hinv65, h_v67⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v66 dropping he_v67 hinv64 e_v67 s64
  step as ⟨e_v68, he_v68⟩
  store_step with CtorSpec.eo__40purify.construct s65 e_v68 (by rw [he_v68]; exact empty_args) hinv65 h64 as ⟨v68, s66, hinv66, h_v68⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v66 h_v67 dropping he_v68 hinv65 e_v68 s65
  step as ⟨e_v69, he_v69⟩
  store_step with CtorSpec.eo_int_2elog2.construct s66 e_v69 (by rw [he_v69]; exact empty_args) hinv66 h64 as ⟨v69, s67, hinv67, h_v69⟩ growing hG carrying h_v2 h_v14 h_v15 h_v57 h_v58 h_v66 h_v67 h_v68 dropping he_v69 hinv66 e_v69 s66
  store_step with Store.apply_rep s67 v69 v2 _ _ hinv67 h64 h_v69 h_v2 (by ns_tac) (by ns_tac) as ⟨v70, s68, hinv68, h_v70⟩ growing hG carrying h_v14 h_v15 h_v57 h_v58 h_v66 h_v67 h_v68 dropping h_v2 h_v69 hinv67 s67 v2 v69
  store_step with Store.apply_rep s68 v68 v70 _ _ hinv68 h64 h_v68 h_v70 (by ns_tac) (by ns_tac) as ⟨v71, s69, hinv69, h_v71⟩ growing hG carrying h_v14 h_v15 h_v57 h_v58 h_v66 h_v67 dropping h_v68 h_v70 hinv68 s68 v68 v70
  store_step with Store.apply_rep s69 v67 v71 _ _ hinv69 h64 h_v67 h_v71 (by ns_tac) (by ns_tac) as ⟨v72, s70, hinv70, h_v72⟩ growing hG carrying h_v14 h_v15 h_v57 h_v58 h_v66 dropping h_v67 h_v71 hinv69 s69 v67 v71
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s70 0#u32 (0) (by scalar_tac) hinv70 h64 as ⟨v73, s71, hinv71, h_v73⟩ growing hG carrying h_v14 h_v15 h_v57 h_v58 h_v66 h_v72 dropping hinv70 s70
  store_step with Store.apply_rep s71 v72 v73 _ _ hinv71 h64 h_v72 h_v73 (by ns_tac) (by ns_tac) as ⟨v74, s72, hinv72, h_v74⟩ growing hG carrying h_v14 h_v15 h_v57 h_v58 h_v66 dropping h_v72 h_v73 hinv71 s71 v72 v73
  store_step with Store.apply_rep s72 v66 v74 _ _ hinv72 h64 h_v66 h_v74 (by ns_tac) (by ns_tac) as ⟨v75, s73, hinv73, h_v75⟩ growing hG carrying h_v14 h_v15 h_v57 h_v58 dropping h_v66 h_v74 hinv72 s72 v66 v74
  store_step with Store.apply_rep s73 v58 v75 _ _ hinv73 h64 h_v58 h_v75 (by ns_tac) (by ns_tac) as ⟨v76, s74, hinv74, h_v76⟩ growing hG carrying h_v14 h_v15 h_v57 dropping h_v58 h_v75 hinv73 s73 v58 v75
  store_step with Store.literal_boolean_spec s74 true hinv74 h64 as ⟨v77, s75, hinv75, h_v77⟩ growing hG carrying h_v14 h_v15 h_v57 h_v76 dropping hinv74 s74
  store_step with Store.apply_rep s75 v76 v77 _ _ hinv75 h64 h_v76 h_v77 (by ns_tac) (by ns_tac) as ⟨v78, s76, hinv76, h_v78⟩ growing hG carrying h_v14 h_v15 h_v57 dropping h_v76 h_v77 hinv75 s75 v76 v77
  store_step with Store.apply_rep s76 v57 v78 _ _ hinv76 h64 h_v57 h_v78 (by ns_tac) (by ns_tac) as ⟨v79, s77, hinv77, h_v79⟩ growing hG carrying h_v14 h_v15 dropping h_v57 h_v78 hinv76 s76 v57 v78
  store_step with Store.apply_rep s77 v15 v79 _ _ hinv77 h64 h_v15 h_v79 (by ns_tac) (by ns_tac) as ⟨v80, s78, hinv78, h_v80⟩ growing hG carrying h_v14 dropping h_v15 h_v79 hinv77 s77 v15 v79
  store_step with Store.literal_boolean_spec s78 true hinv78 h64 as ⟨v81, s79, hinv79, h_v81⟩ growing hG carrying h_v14 h_v80 dropping hinv78 s78
  store_step with Store.apply_rep s79 v80 v81 _ _ hinv79 h64 h_v80 h_v81 (by ns_tac) (by ns_tac) as ⟨v82, s80, hinv80, h_v82⟩ growing hG carrying h_v14 dropping h_v80 h_v81 hinv79 s79 v80 v81
  store_step with Store.apply_rep s80 v14 v82 _ _ hinv80 h64 h_v14 h_v82 (by ns_tac) (by ns_tac) as ⟨v83, s81, hinv81, h_v83⟩ growing hG carrying dropping h_v14 h_v82 hinv80 s80 v14 v82
  case_done hinv81 hG with h_v83 in EoCases.__arith_reduction_pred.case_9 using hn_a0 hn_v1 hn_v2

theorem cases_0_0_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_0 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_1 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_2 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_3 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] = [] ++ [EoCases.__arith_reduction_pred.case_0 x_a0] ++ [EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0
  group_step with case_1_eo__24arith_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] = [EoCases.__arith_reduction_pred.case_0 x_a0] ++ [EoCases.__arith_reduction_pred.case_1 x_a0] ++ [EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hl_0
  group_step with case_2_eo__24arith_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] = [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0] ++ [EoCases.__arith_reduction_pred.case_2 x_a0] ++ [EoCases.__arith_reduction_pred.case_3 x_a0] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hl_0 hl_1
  group_step with case_3_eo__24arith_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] = [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0] ++ [EoCases.__arith_reduction_pred.case_3 x_a0] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_4 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_5 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_6 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_7 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] = [] ++ [EoCases.__arith_reduction_pred.case_4 x_a0] ++ [EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0
  group_step with case_5_eo__24arith_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] = [EoCases.__arith_reduction_pred.case_4 x_a0] ++ [EoCases.__arith_reduction_pred.case_5 x_a0] ++ [EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hl_4
  group_step with case_6_eo__24arith_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] = [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0] ++ [EoCases.__arith_reduction_pred.case_6 x_a0] ++ [EoCases.__arith_reduction_pred.case_7 x_a0] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hl_4 hl_5
  group_step with case_7_eo__24arith_5freduction_5fpred_spec n ih s3 a0 x_a0 hinv3 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] = [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0] ++ [EoCases.__arith_reduction_pred.case_7 x_a0] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_reduction_pred.case_8 x_a0 = none ∧ EoCases.__arith_reduction_pred.case_9 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24arith_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] = [] ++ [EoCases.__arith_reduction_pred.case_8 x_a0] ++ [EoCases.__arith_reduction_pred.case_9 x_a0] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0
  group_step with case_9_eo__24arith_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] = [EoCases.__arith_reduction_pred.case_8 x_a0] ++ [EoCases.__arith_reduction_pred.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hl_8
  group_none hinv2 hG with ⟨hl_8, hl_9⟩

/-- logos's `__arith_reduction_pred` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5freduction_5fpred.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __arith_reduction_pred x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0, EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0, EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __arith_reduction_pred
  unfold EoCases.__arith_reduction_pred.case_0 EoCases.__arith_reduction_pred.case_1 EoCases.__arith_reduction_pred.case_2 EoCases.__arith_reduction_pred.case_3 EoCases.__arith_reduction_pred.case_4 EoCases.__arith_reduction_pred.case_5 EoCases.__arith_reduction_pred.case_6 EoCases.__arith_reduction_pred.case_7 EoCases.__arith_reduction_pred.case_8 EoCases.__arith_reduction_pred.case_9
  logos_eq

theorem body_eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24arith_5freduction_5fpred s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_reduction_pred x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5freduction_5fpred.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24arith_5freduction_5fpred
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5freduction_5fpred_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0, EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0, EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] = [] ++ [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] ++ [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0, EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0
  body_group_step with cases_0_1_eo__24arith_5freduction_5fpred_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0, EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0, EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] = [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0] ++ [EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] ++ [EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24arith_5freduction_5fpred_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0
    split (show [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0, EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0, EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] = [EoCases.__arith_reduction_pred.case_0 x_a0, EoCases.__arith_reduction_pred.case_1 x_a0, EoCases.__arith_reduction_pred.case_2 x_a0, EoCases.__arith_reduction_pred.case_3 x_a0, EoCases.__arith_reduction_pred.case_4 x_a0, EoCases.__arith_reduction_pred.case_5 x_a0, EoCases.__arith_reduction_pred.case_6 x_a0, EoCases.__arith_reduction_pred.case_7 x_a0] ++ [EoCases.__arith_reduction_pred.case_8 x_a0, EoCases.__arith_reduction_pred.case_9 x_a0] ++ [] from rfl)
    otherwise ⟨hl_8, hl_9⟩ using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hn_a0 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 in EoCases.__arith_reduction_pred.case_0 EoCases.__arith_reduction_pred.case_1 EoCases.__arith_reduction_pred.case_2 EoCases.__arith_reduction_pred.case_3 EoCases.__arith_reduction_pred.case_4 EoCases.__arith_reduction_pred.case_5 EoCases.__arith_reduction_pred.case_6 EoCases.__arith_reduction_pred.case_7 EoCases.__arith_reduction_pred.case_8 EoCases.__arith_reduction_pred.case_9

theorem eo__24arith_5freduction_5fpred_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5freduction_5fpred.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24arith_5freduction_5fpred
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5freduction_5fpred s1 a0) (fun s' t => Represents.rep s' t (__arith_reduction_pred x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5freduction_5fpred_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_2 using hn_a0 hn_a1 hn_a2

theorem case_3_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_3 using hn_a0 hn_a1 hn_a2

theorem case_4_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_inv.case_4 using hn_a0 hn_a1 hn_a2

theorem cases_0_0_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2 = none ∧ EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2 = none ∧ EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2 = none ∧ EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5frel_5finv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [] ++ [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2
  group_step with case_1_eo__24arith_5frel_5finv_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hl_0
  group_step with case_2_eo__24arith_5frel_5finv_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1
  group_step with case_3_eo__24arith_5frel_5finv_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5frel_5finv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] = [] ++ [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2
  group_none hinv1 hG with hl_4

/-- logos's `__arith_rel_inv` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5finv.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __arith_rel_inv x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_inv
  unfold EoCases.__arith_rel_inv.case_0 EoCases.__arith_rel_inv.case_1 EoCases.__arith_rel_inv.case_2 EoCases.__arith_rel_inv.case_3 EoCases.__arith_rel_inv.case_4
  logos_eq

theorem body_eo__24arith_5frel_5finv_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24arith_5frel_5finv s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_inv x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5finv.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24arith_5frel_5finv
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5frel_5finv_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] = [] ++ [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2
  body_group_step with cases_0_1_eo__24arith_5frel_5finv_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2
    split (show [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] = [EoCases.__arith_rel_inv.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_inv.case_3 x_a0 x_a1 x_a2] ++ [EoCases.__arith_rel_inv.case_4 x_a0 x_a1 x_a2] ++ [] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hl_0 hl_1 hl_2 hl_3 hl_4 in EoCases.__arith_rel_inv.case_0 EoCases.__arith_rel_inv.case_1 EoCases.__arith_rel_inv.case_2 EoCases.__arith_rel_inv.case_3 EoCases.__arith_rel_inv.case_4

theorem eo__24arith_5frel_5finv_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5finv.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24arith_5frel_5finv
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5finv s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__arith_rel_inv x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5finv_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_2 using hn_a0 hn_a1 hn_a2

theorem case_3_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_neg.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_neg.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 dropping he_v0 e_v0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a1 h_a2 dropping h_a0 h_v0 he_v1 hinv1 e_v1 s1 v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a2 dropping h_a1 h_v1 hinv2 s2 v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying dropping h_a2 h_v2 hinv3 s3 v2
  case_done hinv4 hG with h_v3 in EoCases.__arith_rel_neg.case_3 using hn_a0 hn_a1 hn_a2

/-- logos's `__arith_rel_neg` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5fneg.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __arith_rel_neg x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_neg.case_0 x_a0 x_a1 x_a2, EoCases.__arith_rel_neg.case_1 x_a0 x_a1 x_a2, EoCases.__arith_rel_neg.case_2 x_a0 x_a1 x_a2, EoCases.__arith_rel_neg.case_3 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_neg
  unfold EoCases.__arith_rel_neg.case_0 EoCases.__arith_rel_neg.case_1 EoCases.__arith_rel_neg.case_2 EoCases.__arith_rel_neg.case_3
  logos_eq

theorem body_eo__24arith_5frel_5fneg_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24arith_5frel_5fneg s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_neg x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5fneg.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24arith_5frel_5fneg
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24arith_5frel_5fneg_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24arith_5frel_5fneg_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24arith_5frel_5fneg_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  case_step with case_3_eo__24arith_5frel_5fneg_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 hc3 in EoCases.__arith_rel_neg.case_0 EoCases.__arith_rel_neg.case_1 EoCases.__arith_rel_neg.case_2 EoCases.__arith_rel_neg.case_3

theorem eo__24arith_5frel_5fneg_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5fneg.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24arith_5frel_5fneg
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5fneg s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__arith_rel_neg x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5fneg_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
