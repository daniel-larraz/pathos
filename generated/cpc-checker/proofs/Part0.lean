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
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__abconv_ubv_to_int_elim.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__abconv_ubv_to_int_elim.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s2 0#u32 (0) (by scalar_tac) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__abconv_ubv_to_int_elim.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_1_eo__24abconv_5fubv_5fto_5fint_5felim_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24abconv_5fubv_5fto_5fint_5felim s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__abconv_ubv_to_int_elim.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__abconv_ubv_to_int_elim.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24abconv_5fubv_5fto_5fint_5felim more_0_eo__24abconv_5fubv_5fto_5fint_5felim
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__abconv_ubv_to_int_elim.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__abconv_ubv_to_int_elim.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__abconv_ubv_to_int_elim.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__2b.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo_ite.construct s2 e_v8 (by rw [he_v8]; exact empty_args) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  step as ⟨e_v9, he_v9⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v9 (by rw [he_v9]; exact empty_args) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with CtorSpec.eo_extract.construct s4 e_v10 (by rw [he_v10]; rfl) h_v5 h_v5 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_rep s5 v10 a0 _ _ hinv5 h64 h_v10 h_a0 (by ns_tac) (by ns_tac) as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_rep s6 v9 v11 _ _ hinv6 h64 h_v9 h_v11 (by ns_tac) (by ns_tac) as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s7 1#u32 1#u32 (1) (1) rfl rfl (by unfold Tree.okBv; norm_num) hinv7 h64 as ⟨v13, s8, hinv8, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12
  store_step with Store.apply_rep s8 v12 v13 _ _ hinv8 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s9, hinv9, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13
  store_step with Store.apply_rep s9 v8 v14 _ _ hinv9 h64 h_v8 h_v14 (by ns_tac) (by ns_tac) as ⟨v15, s10, hinv10, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s10 v15 a2 _ _ hinv10 h64 h_v15 h_a2 (by ns_tac) (by ns_tac) as ⟨v16, s11, hinv11, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s11 0#u32 (0) (by scalar_tac) hinv11 h64 as ⟨v17, s12, hinv12, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s12 v16 v17 _ _ hinv12 h64 h_v16 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s13, hinv13, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s13 v7 v18 _ _ hinv13 h64 h_v7 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s14, hinv14, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s14 2#u32 (2) (by scalar_tac) hinv14 h64 as ⟨v20, s15, hinv15, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  step as ⟨e_v21, he_v21⟩
  store_step with Store.builtin_spec_mul s15 e_v21 (by rw [he_v21]; rfl) h_a2 h_v20 hinv15 h64 as ⟨v21, s16, hinv16, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with ih.eo__24abconv_5fubv_5fto_5fint_5felim s16 a0 v2 v21 _ _ _ hinv16 h64 (hG.rem hrem) h_a0 h_v2 h_v21 as ⟨v22, s17, hinv17, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_mk_rep s17 v19 v22 _ _ hinv17 h64 h_v19 h_v22 as ⟨v23, s18, hinv18, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
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
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_one.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
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
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_one.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v0
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
  store_step with CtorSpec.eo_Int.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_zero.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 0#u32 (0) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
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
  store_step with CtorSpec.eo_Real.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_mk_zero.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v0
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
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_not.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6
  pat_same v5 v7 with h_v5 h_v7 using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v6 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__arith_normalize_lit.case_0
  store_step with Store.apply_rep s2 v12 v13 _ _ hinv2 h64 h_v12 h_v13 (by ns_tac) (by ns_tac) as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13
  store_step with Store.apply_rep s3 v14 v10 _ _ hinv3 h64 h_v14 h_v10 (by ns_tac) (by ns_tac) as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14
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
  store_step with CtorSpec.eo_not.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  pat_unapply h_v2 as ⟨v5, v6, x_v5, x_v6, h_v5, h_v6, hn_v5, hn_v6⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  pat_unapply h_v5 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__arith_normalize_lit.case_1
  store_step with ih.eo__24arith_5frel_5fneg s1 v8 v9 v6 _ _ _ hinv1 h64 (hG.rem hrem) h_v8 h_v9 h_v6 as ⟨v10, s2, hinv2, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v5 h_v6 h_v8 h_v9
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
  store_step with Store.apply_rep s v4 v5 _ _ hinv h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  store_step with Store.apply_rep s1 v6 v2 _ _ hinv1 h64 h_v6 h_v2 (by ns_tac) (by ns_tac) as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
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
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3e_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_inv.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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
  store_step with CtorSpec.eo__3e_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_neg.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
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

theorem case_0_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_1_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_1 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_2_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_2 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_3_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_3 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_4_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_4 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_5_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_5_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c_3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_5
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_5
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_5 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_6_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_6_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_6
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_6
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_6 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_7_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_7_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_7
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_7
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_7 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_8_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_8_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_sum.case_8
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c_3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_sum.case_8
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c_3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_sum.case_8 using hn_a0 hn_a1 hn_a2 hn_a3

theorem cases_0_0_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_1_eo__24arith_5frel_5fsum_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0
  group_step with case_2_eo__24arith_5frel_5fsum_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1
  group_step with case_3_eo__24arith_5frel_5fsum_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_5_eo__24arith_5frel_5fsum_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4
  group_step with case_6_eo__24arith_5frel_5fsum_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4 hl_5
  group_step with case_7_eo__24arith_5frel_5fsum_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_none hinv1 hG with hl_8

/-- logos's `__arith_rel_sum` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5fsum.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __arith_rel_sum x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_sum
  unfold EoCases.__arith_rel_sum.case_0 EoCases.__arith_rel_sum.case_1 EoCases.__arith_rel_sum.case_2 EoCases.__arith_rel_sum.case_3 EoCases.__arith_rel_sum.case_4 EoCases.__arith_rel_sum.case_5 EoCases.__arith_rel_sum.case_6 EoCases.__arith_rel_sum.case_7 EoCases.__arith_rel_sum.case_8
  logos_eq

theorem body_eo__24arith_5frel_5fsum_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24arith_5frel_5fsum s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_sum x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5fsum.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24arith_5frel_5fsum
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5frel_5fsum_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  body_group_step with cases_0_1_eo__24arith_5frel_5fsum_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3
  body_group_step with cases_0_2_eo__24arith_5frel_5fsum_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_sum.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_5 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_6 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_sum.case_7 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_sum.case_8 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  body_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 in EoCases.__arith_rel_sum.case_0 EoCases.__arith_rel_sum.case_1 EoCases.__arith_rel_sum.case_2 EoCases.__arith_rel_sum.case_3 EoCases.__arith_rel_sum.case_4 EoCases.__arith_rel_sum.case_5 EoCases.__arith_rel_sum.case_6 EoCases.__arith_rel_sum.case_7 EoCases.__arith_rel_sum.case_8

theorem eo__24arith_5frel_5fsum_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5fsum.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24arith_5frel_5fsum
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5fsum s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__arith_rel_sum x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5fsum_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_0_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_0
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3e.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_0 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_1_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_1_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_1
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_1 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_2_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_2_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_2
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3c.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_2 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_3_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_3_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_3
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3e.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_3 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_4_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_4_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3e.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_4
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3c.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_4
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_4 using hn_a0 hn_a1 hn_a2 hn_a3

theorem case_5_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    case_5_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3c.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__arith_rel_trichotomy.case_5
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3e.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__arith_rel_trichotomy.case_5
  step as ⟨e_v2, he_v2⟩
  store_step with CtorSpec.eo__3d.construct s2 e_v2 (by rw [he_v2]; exact empty_args) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a3 _ _ hinv4 h64 h_v3 h_a3 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_v0 h_v1 h_v2 h_v3
  case_done hinv5 hG with h_v4 in EoCases.__arith_rel_trichotomy.case_5 using hn_a0 hn_a1 hn_a2 hn_a3

theorem cases_0_0_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24arith_5frel_5ftrichotomy_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_1_eo__24arith_5frel_5ftrichotomy_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0
  group_step with case_2_eo__24arith_5frel_5ftrichotomy_spec n ih s2 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1
  group_step with case_3_eo__24arith_5frel_5ftrichotomy_spec n ih s3 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) (hn_a3 : x_a3 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3 = none ∧ EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24arith_5frel_5ftrichotomy_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  group_step with case_5_eo__24arith_5frel_5ftrichotomy_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_4
  group_none hinv2 hG with ⟨hl_4, hl_5⟩

/-- logos's `__arith_rel_trichotomy` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24arith_5frel_5ftrichotomy.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) :
    __arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else if x_a3 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] HasStuck.stuck) := by
  conv => lhs; unfold __arith_rel_trichotomy
  unfold EoCases.__arith_rel_trichotomy.case_0 EoCases.__arith_rel_trichotomy.case_1 EoCases.__arith_rel_trichotomy.case_2 EoCases.__arith_rel_trichotomy.case_3 EoCases.__arith_rel_trichotomy.case_4 EoCases.__arith_rel_trichotomy.case_5
  logos_eq

theorem body_eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) :
    body_eo__24arith_5frel_5ftrichotomy s a0 a1 a2 a3 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24arith_5frel_5ftrichotomy.rust_eq x_a0 x_a1 x_a2 x_a3 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3)]
  unfold body_eo__24arith_5frel_5ftrichotomy
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  stuck_check h_a3 : x_a3 as hn_a3 else hinv hG
  body_group_step with cases_0_0_eo__24arith_5frel_5ftrichotomy_spec n ih s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [] ++ [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1 hn_a2 hn_a3
  body_group_step with cases_0_1_eo__24arith_5frel_5ftrichotomy_spec n ih s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 hn_a0 hn_a1 hn_a2 hn_a3
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3
    split (show [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] = [EoCases.__arith_rel_trichotomy.case_0 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_1 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_2 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_3 x_a0 x_a1 x_a2 x_a3] ++ [EoCases.__arith_rel_trichotomy.case_4 x_a0 x_a1 x_a2 x_a3, EoCases.__arith_rel_trichotomy.case_5 x_a0 x_a1 x_a2 x_a3] ++ [] from rfl)
    otherwise ⟨hl_4, hl_5⟩ using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hn_a3 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 in EoCases.__arith_rel_trichotomy.case_0 EoCases.__arith_rel_trichotomy.case_1 EoCases.__arith_rel_trichotomy.case_2 EoCases.__arith_rel_trichotomy.case_3 EoCases.__arith_rel_trichotomy.case_4 EoCases.__arith_rel_trichotomy.case_5

theorem eo__24arith_5frel_5ftrichotomy_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24arith_5frel_5ftrichotomy.Spec n := by
  intro s a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv h64 hrem h_a0 h_a1 h_a2 h_a3
  unfold eo__24arith_5frel_5ftrichotomy
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24arith_5frel_5ftrichotomy s1 a0 a1 a2 a3) (fun s' t => Represents.rep s' t (__arith_rel_trichotomy x_a0 x_a1 x_a2 x_a3))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24arith_5frel_5ftrichotomy_spec m (ih m hm) s1 a0 a1 a2 a3 x_a0 x_a1 x_a2 x_a3 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2 = some (__assoc_nil_nth y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24assoc_5fnil_5fnth
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_0
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__assoc_nil_nth.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same a2 v6 with h_a2 h_v6 using hinv1 else hinv1 hG in EoCases.__assoc_nil_nth.case_0
  case_done hinv1 hG with h_v5 in EoCases.__assoc_nil_nth.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2 = some (__assoc_nil_nth y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24assoc_5fnil_5fnth
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__assoc_nil_nth.case_1
  pat_same v4 a0 with h_v4 h_a0 using hinv else hinv hG in EoCases.__assoc_nil_nth.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s 1#u32 (-1) (by scalar_tac) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with Store.builtin_spec_add s1 e_v7 (by rw [he_v7]; rfl) h_a2 h_v6 hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  case_again hinv2 hG with h_a0 h_v2 h_v7 in EoCases.__assoc_nil_nth.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__assoc_nil_nth` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24assoc_5fnil_5fnth.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __assoc_nil_nth x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__assoc_nil_nth.case_0 x_a0 x_a1 x_a2, EoCases.__assoc_nil_nth.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __assoc_nil_nth
  unfold EoCases.__assoc_nil_nth.case_0 EoCases.__assoc_nil_nth.case_1
  try unfold Eo.__eo_l_1___assoc_nil_nth
  logos_eq_deep

theorem step_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __assoc_nil_nth x_a0 x_a1 x_a2 = __assoc_nil_nth y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24assoc_5fnil_5fnth.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24assoc_5fnil_5fnth
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24assoc_5fnil_5fnth_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24assoc_5fnil_5fnth_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__assoc_nil_nth.case_0 EoCases.__assoc_nil_nth.case_1

theorem body_eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24assoc_5fnil_5fnth s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24assoc_5fnil_5fnth body_eo__24assoc_5fnil_5fnth_loop
  step with step_eo__24assoc_5fnil_5fnth_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24assoc_5fnil_5fnth at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24assoc_5fnil_5fnth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24assoc_5fnil_5fnth.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24assoc_5fnil_5fnth
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 14#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24assoc_5fnil_5fnth s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__assoc_nil_nth x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_14 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_14 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24assoc_5fnil_5fnth_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_binary.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_binary.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fapply_5fbinary
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_binary.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_bitblast_apply_binary.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_binary.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_binary.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fapply_5fbinary more_0_eo__24bv_5fbitblast_5fapply_5fbinary
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_binary.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_binary.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_1
  pat_unapply h_a2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_binary.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_binary.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  store_step with ih.eo__24bv_5fbitblast_5fbinary_5fapp s3 a0 v5 v12 _ _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v5 h_v12 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_mk_rep s4 v14 v15 _ _ hinv4 h64 h_v14 h_v15 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fbinary s5 a0 v2 v9 _ _ _ hinv5 h64 (hG.rem hrem) h_a0 h_v2 h_v9 as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_mk_rep s6 v16 v17 _ _ hinv6 h64 h_v16 h_v17 as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  case_done hinv7 hG with h_v18 in EoCases.__bv_bitblast_apply_binary.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_apply_binary` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fapply_5fbinary.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_apply_binary x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_apply_binary.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_apply_binary.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_apply_binary
  unfold EoCases.__bv_bitblast_apply_binary.case_0 EoCases.__bv_bitblast_apply_binary.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fapply_5fbinary s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_binary x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fapply_5fbinary.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fapply_5fbinary
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fapply_5fbinary_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fapply_5fbinary_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_apply_binary.case_0 EoCases.__bv_bitblast_apply_binary.case_1

theorem eo__24bv_5fbitblast_5fapply_5fbinary_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fapply_5fbinary.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fapply_5fbinary
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 17#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fapply_5fbinary s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_apply_binary x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_17 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_17 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fapply_5fbinary_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_ite.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_ite.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fapply_5fite
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_ite.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_bitblast_apply_ite.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_ite.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_ite.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fapply_5fite more_0_eo__24bv_5fbitblast_5fapply_5fite
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_ite.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_ite.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_1
  pat_unapply h_a2 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_ite.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_apply_ite.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_ite.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s4 v15 a0 _ _ hinv4 h64 h_v15 h_a0 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s7 v14 v18 _ _ hinv7 h64 h_v14 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with ih.eo__24bv_5fbitblast_5fapply_5fite s8 a0 v2 v9 _ _ _ hinv8 h64 (hG.rem hrem) h_a0 h_v2 h_v9 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_mk_rep s9 v19 v20 _ _ hinv9 h64 h_v19 h_v20 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  case_done hinv10 hG with h_v21 in EoCases.__bv_bitblast_apply_ite.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_apply_ite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fapply_5fite.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_apply_ite x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_apply_ite.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_apply_ite.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_apply_ite
  unfold EoCases.__bv_bitblast_apply_ite.case_0 EoCases.__bv_bitblast_apply_ite.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fapply_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fapply_5fite.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fapply_5fite
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fapply_5fite_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fapply_5fite_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_apply_ite.case_0 EoCases.__bv_bitblast_apply_ite.case_1

theorem eo__24bv_5fbitblast_5fapply_5fite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fapply_5fite.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fapply_5fite
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 18#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fapply_5fite s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_apply_ite x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_18 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_18 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fapply_5fite_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_unary.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_unary.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fapply_5funary
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_unary.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_apply_unary.case_0 using hn_a0 hn_a1

theorem case_1_eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_apply_unary.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_apply_unary.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fapply_5funary
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_unary.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_apply_unary.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_apply_unary.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 a0 v5 _ _ hinv2 h64 h_a0 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v7 v8 _ _ hinv3 h64 h_v7 h_v8 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24bv_5fbitblast_5fapply_5funary s4 a0 v2 _ _ hinv4 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with Store.apply_mk_rep s5 v9 v10 _ _ hinv5 h64 h_v9 h_v10 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  case_done hinv6 hG with h_v11 in EoCases.__bv_bitblast_apply_unary.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_apply_unary` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fapply_5funary.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_bitblast_apply_unary x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_apply_unary.case_0 x_a0 x_a1, EoCases.__bv_bitblast_apply_unary.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_apply_unary
  unfold EoCases.__bv_bitblast_apply_unary.case_0 EoCases.__bv_bitblast_apply_unary.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fbitblast_5fapply_5funary s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_apply_unary x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fapply_5funary.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fbitblast_5fapply_5funary
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fapply_5funary_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fbitblast_5fapply_5funary_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_bitblast_apply_unary.case_0 EoCases.__bv_bitblast_apply_unary.case_1

theorem eo__24bv_5fbitblast_5fapply_5funary_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fapply_5funary.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fbitblast_5fapply_5funary
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 19#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fapply_5funary s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_bitblast_apply_unary x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_19 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_19 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fapply_5funary_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_and.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_and.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s5 true hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__bv_bitblast_binary_app.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_or.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_or.construct s3 e_v3 (by rw [he_v3]; exact empty_args) hinv3 h64 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  store_step with Store.apply_rep s4 v3 a2 _ _ hinv4 h64 h_v3 h_a2 (by ns_tac) (by ns_tac) as ⟨v4, s5, hinv5, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3
  store_step with Store.literal_boolean_spec s5 false hinv5 h64 as ⟨v5, s6, hinv6, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_rep s6 v4 v5 _ _ hinv6 h64 h_v4 h_v5 (by ns_tac) (by ns_tac) as ⟨v6, s7, hinv7, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5
  store_step with Store.apply_rep s7 v2 v6 _ _ hinv7 h64 h_v2 h_v6 (by ns_tac) (by ns_tac) as ⟨v7, s8, hinv8, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2 h_v3 h_v4 h_v5 h_v6
  case_done hinv8 hG with h_v7 in EoCases.__bv_bitblast_binary_app.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_xor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_xor.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__bv_bitblast_binary_app.case_2 using hn_a0 hn_a1 hn_a2

theorem case_3_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_3_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_binary_app.case_3 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_binary_app.case_3 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__3d.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_binary_app.case_3
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__3d.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  store_step with Store.apply_rep s2 v1 a1 _ _ hinv2 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with Store.apply_rep s3 v2 a2 _ _ hinv3 h64 h_v2 h_a2 (by ns_tac) (by ns_tac) as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__bv_bitblast_binary_app.case_3 using hn_a0 hn_a1 hn_a2

/-- logos's `__bv_bitblast_binary_app` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fbinary_5fapp.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_binary_app x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_binary_app.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_binary_app.case_1 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_binary_app.case_2 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_binary_app.case_3 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_binary_app
  unfold EoCases.__bv_bitblast_binary_app.case_0 EoCases.__bv_bitblast_binary_app.case_1 EoCases.__bv_bitblast_binary_app.case_2 EoCases.__bv_bitblast_binary_app.case_3
  logos_eq

theorem body_eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fbinary_5fapp s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_binary_app x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fbinary_5fapp.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fbinary_5fapp
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  case_step with case_2_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1
  case_step with case_3_eo__24bv_5fbitblast_5fbinary_5fapp_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2
  body_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 hc3 in EoCases.__bv_bitblast_binary_app.case_0 EoCases.__bv_bitblast_binary_app.case_1 EoCases.__bv_bitblast_binary_app.case_2 EoCases.__bv_bitblast_binary_app.case_3

theorem eo__24bv_5fbitblast_5fbinary_5fapp_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fbinary_5fapp.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fbinary_5fapp
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fbinary_5fapp s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_binary_app x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fbinary_5fapp_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_concat.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_concat.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fconcat
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_concat.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_concat.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_concat.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with ih.eo__24bv_5fbitblast_5fconcat s3 v2 a1 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_mk_rep s4 v8 v9 _ _ hinv4 h64 h_v8 h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__bv_bitblast_concat.case_0 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_concat.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_concat.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fconcat
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_concat.case_1
  case_done hinv1 hG with h_a1 in EoCases.__bv_bitblast_concat.case_1 using hn_a0 hn_a1

/-- logos's `__bv_bitblast_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fconcat.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_bitblast_concat x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_concat.case_0 x_a0 x_a1, EoCases.__bv_bitblast_concat.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_concat
  unfold EoCases.__bv_bitblast_concat.case_0 EoCases.__bv_bitblast_concat.case_1
  logos_eq

theorem body_eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fbitblast_5fconcat s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_concat x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fconcat.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fbitblast_5fconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fconcat_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fbitblast_5fconcat_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_bitblast_concat.case_0 EoCases.__bv_bitblast_concat.case_1

theorem eo__24bv_5fbitblast_5fconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fconcat.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fbitblast_5fconcat
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 21#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fconcat s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_bitblast_concat x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_21 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_21 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fconcat_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fhead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fhead s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_head.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_head.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fhead
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_head.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_head.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_head.case_0
  case_done hinv1 hG with h_v5 in EoCases.__bv_bitblast_head.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_head` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fhead.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_bitblast_head x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_head.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_head
  unfold EoCases.__bv_bitblast_head.case_0
  logos_eq

theorem body_eo__24bv_5fbitblast_5fhead_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fbitblast_5fhead s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_head x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fhead.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fbitblast_5fhead
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fhead_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_bitblast_head.case_0

theorem eo__24bv_5fbitblast_5fhead_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fhead.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fbitblast_5fhead
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fhead s1 a0) (fun s' t => Represents.rep s' t (__bv_bitblast_head x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fhead_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_prefix.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_prefix.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_prefix.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_prefix.case_0 using hn_a0 hn_a1

theorem case_1_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_prefix.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_prefix.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_prefix.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_prefix.case_1 using hn_a0 hn_a1

theorem case_2_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_prefix.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_prefix.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_prefix.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_prefix.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_prefix.case_2
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s3 1#u32 (-1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_add s4 e_v10 (by rw [he_v10]; rfl) h_a0 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24bv_5fbitblast_5fprefix s5 v10 v2 _ _ hinv5 h64 (hG.rem hrem) h_v10 h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v8 v11 _ _ hinv6 h64 h_v8 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__bv_bitblast_prefix.case_2 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_prefix` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fprefix.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_bitblast_prefix x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_prefix.case_0 x_a0 x_a1, EoCases.__bv_bitblast_prefix.case_1 x_a0 x_a1, EoCases.__bv_bitblast_prefix.case_2 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_prefix
  unfold EoCases.__bv_bitblast_prefix.case_0 EoCases.__bv_bitblast_prefix.case_1 EoCases.__bv_bitblast_prefix.case_2
  logos_eq

theorem body_eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fbitblast_5fprefix s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_prefix x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fprefix.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fbitblast_5fprefix
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fprefix_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fbitblast_5fprefix_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  case_step with case_2_eo__24bv_5fbitblast_5fprefix_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0 hc1
  body_stuck hinv3 hG using hn_a0 hn_a1 hc0 hc1 hc2 in EoCases.__bv_bitblast_prefix.case_0 EoCases.__bv_bitblast_prefix.case_1 EoCases.__bv_bitblast_prefix.case_2

theorem eo__24bv_5fbitblast_5fprefix_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fprefix.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fbitblast_5fprefix
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 23#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fprefix s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_bitblast_prefix x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_23 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_23 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fprefix_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2 = some (__bv_bitblast_subsequence y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a2 v0 with h_a2 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_subsequence.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_bitblast_subsequence.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2 = some (__bv_bitblast_subsequence y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_subsequence.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s1 1#u32 (1) (by scalar_tac) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  step as ⟨e_v2, he_v2⟩
  store_step with Store.builtin_spec_add s2 e_v2 (by rw [he_v2]; rfl) h_a1 h_v1 hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1
  store_step with ih.eo__24bv_5fbitblast_5fprefix s3 v2 a2 _ _ hinv3 h64 (hG.rem hrem) h_v2 h_a2 as ⟨v3, s4, hinv4, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0 h_v1 h_v2
  case_done hinv4 hG with h_v3 in EoCases.__bv_bitblast_subsequence.case_1 using hn_a0 hn_a1 hn_a2

theorem case_2_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_2_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2 = some (__bv_bitblast_subsequence y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  pat_unapply h_a2 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_subsequence.case_2
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_subsequence.case_2
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_subsequence.case_2
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s1 1#u32 (-1) (by scalar_tac) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with Store.builtin_spec_add s2 e_v8 (by rw [he_v8]; rfl) h_a0 h_v7 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s3 1#u32 (-1) (by scalar_tac) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  step as ⟨e_v10, he_v10⟩
  store_step with Store.builtin_spec_add s4 e_v10 (by rw [he_v10]; rfl) h_a1 h_v9 hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_again hinv5 hG with h_v8 h_v10 h_v2 in EoCases.__bv_bitblast_subsequence.case_2 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_subsequence` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fsubsequence.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_subsequence x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_subsequence.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_subsequence.case_1 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_subsequence.case_2 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_subsequence
  unfold EoCases.__bv_bitblast_subsequence.case_0 EoCases.__bv_bitblast_subsequence.case_1 EoCases.__bv_bitblast_subsequence.case_2
  logos_eq

theorem step_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __bv_bitblast_subsequence x_a0 x_a1 x_a2 = __bv_bitblast_subsequence y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fsubsequence.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24bv_5fbitblast_5fsubsequence
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24bv_5fbitblast_5fsubsequence_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24bv_5fbitblast_5fsubsequence_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_step with case_2_eo__24bv_5fbitblast_5fsubsequence_spec n ih s3 a0 a1 a2 x_a0 x_a1 x_a2 hinv3 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s4, hinv4, hc2⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0 hc1
  round_stuck hinv4 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 hc2 in EoCases.__bv_bitblast_subsequence.case_0 EoCases.__bv_bitblast_subsequence.case_1 EoCases.__bv_bitblast_subsequence.case_2

theorem body_eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24bv_5fbitblast_5fsubsequence s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24bv_5fbitblast_5fsubsequence body_eo__24bv_5fbitblast_5fsubsequence_loop
  step with step_eo__24bv_5fbitblast_5fsubsequence_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24bv_5fbitblast_5fsubsequence at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fbitblast_5fsubsequence_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fsubsequence.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fsubsequence
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 25#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fsubsequence s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_subsequence x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_25 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_25 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fsubsequence_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5ftail_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5ftail s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_tail.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_tail.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5ftail
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_tail.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_tail.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_tail.case_0
  case_done hinv1 hG with h_v2 in EoCases.__bv_bitblast_tail.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_bitblast_tail` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5ftail.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_bitblast_tail x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_tail.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_tail
  unfold EoCases.__bv_bitblast_tail.case_0
  logos_eq

theorem body_eo__24bv_5fbitblast_5ftail_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fbitblast_5ftail s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_tail x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5ftail.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fbitblast_5ftail
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5ftail_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_bitblast_tail.case_0

theorem eo__24bv_5fbitblast_5ftail_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5ftail.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fbitblast_5ftail
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5ftail s1 a0) (fun s' t => Represents.rep s' t (__bv_bitblast_tail x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5ftail_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fult s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitblast_ult.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitblast_ult.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fult
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult.case_0
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult.case_0
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult.case_0
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_ult.case_0
  have h_ite_v42 := (show if_1_eo__24bv_5fbitblast_5fult s2 a2 v5 v12 ⦃ r s' => s'.Inv ∧ s2.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_1_eo__24bv_5fbitblast_5fult more_0_eo__24bv_5fbitblast_5fult
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s2
    rcases Store.boolean_value_term h_a2 with ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩ | ⟨hx_14, hbv_14⟩
    · ite_branch hbv_14
      step as ⟨e_v14, he_v14⟩
      store_step with CtorSpec.eo_or.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
      step as ⟨e_v15, he_v15⟩
      store_step with CtorSpec.eo_and.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
      step as ⟨e_v16, he_v16⟩
      store_step with CtorSpec.eo_not.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
      store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
      store_step with Store.apply_rep s6 v15 v17 _ _ hinv6 h64 h_v15 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
      step as ⟨e_v19, he_v19⟩
      store_step with CtorSpec.eo_and.construct s7 e_v19 (by rw [he_v19]; exact empty_args) hinv7 h64 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
      store_step with Store.apply_rep s8 v19 v12 _ _ hinv8 h64 h_v19 h_v12 (by ns_tac) (by ns_tac) as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
      store_step with Store.literal_boolean_spec s9 true hinv9 h64 as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
      store_step with Store.apply_rep s10 v20 v21 _ _ hinv10 h64 h_v20 h_v21 (by ns_tac) (by ns_tac) as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
      store_step with Store.apply_rep s11 v18 v22 _ _ hinv11 h64 h_v18 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
      store_step with Store.apply_rep s12 v14 v23 _ _ hinv12 h64 h_v14 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
      step as ⟨e_v25, he_v25⟩
      store_step with CtorSpec.eo_or.construct s13 e_v25 (by rw [he_v25]; exact empty_args) hinv13 h64 as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
      step as ⟨e_v26, he_v26⟩
      store_step with CtorSpec.eo__3d.construct s14 e_v26 (by rw [he_v26]; exact empty_args) hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
      store_step with Store.apply_rep s15 v26 v5 _ _ hinv15 h64 h_v26 h_v5 (by ns_tac) (by ns_tac) as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
      store_step with Store.apply_rep s16 v27 v12 _ _ hinv16 h64 h_v27 h_v12 (by ns_tac) (by ns_tac) as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
      store_step with Store.apply_rep s17 v25 v28 _ _ hinv17 h64 h_v25 h_v28 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
      store_step with Store.literal_boolean_spec s18 false hinv18 h64 as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
      store_step with Store.apply_rep s19 v29 v30 _ _ hinv19 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
      store_step with Store.apply_rep s20 v24 v31 _ _ hinv20 h64 h_v24 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
      ite_done hinv21 hG with (eo_ite_true_rep _ hx_14 h_v32)
    · ite_branch hbv_14
      step as ⟨e_v33, he_v33⟩
      store_step with CtorSpec.eo_and.construct s2 e_v33 (by rw [he_v33]; exact empty_args) hinv2 h64 as ⟨v33, s3, hinv3, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
      step as ⟨e_v34, he_v34⟩
      store_step with CtorSpec.eo_not.construct s3 e_v34 (by rw [he_v34]; exact empty_args) hinv3 h64 as ⟨v34, s4, hinv4, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33
      store_step with Store.apply_rep s4 v34 v5 _ _ hinv4 h64 h_v34 h_v5 (by ns_tac) (by ns_tac) as ⟨v35, s5, hinv5, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34
      store_step with Store.apply_rep s5 v33 v35 _ _ hinv5 h64 h_v33 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s6, hinv6, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34 h_v35
      step as ⟨e_v37, he_v37⟩
      store_step with CtorSpec.eo_and.construct s6 e_v37 (by rw [he_v37]; exact empty_args) hinv6 h64 as ⟨v37, s7, hinv7, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34 h_v35 h_v36
      store_step with Store.apply_rep s7 v37 v12 _ _ hinv7 h64 h_v37 h_v12 (by ns_tac) (by ns_tac) as ⟨v38, s8, hinv8, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34 h_v35 h_v36 h_v37
      store_step with Store.literal_boolean_spec s8 true hinv8 h64 as ⟨v39, s9, hinv9, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
      store_step with Store.apply_rep s9 v38 v39 _ _ hinv9 h64 h_v38 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s10, hinv10, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
      store_step with Store.apply_rep s10 v36 v40 _ _ hinv10 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s11, hinv11, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
      ite_done hinv11 hG with (eo_ite_false_rep _ hx_14 h_v41)
    · ite_branch hbv_14
      ite_stuck hinv2 hG with hx_14)
  store_step with h_ite_v42 as ⟨v42, s3, hinv3, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  store_step with ih.eo__24bv_5fbitblast_5fult_5frec s3 v2 v9 v42 _ _ _ hinv3 h64 (hG.rem hrem) h_v2 h_v9 h_v42 as ⟨v43, s4, hinv4, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v42
  case_done hinv4 hG with h_v43 in EoCases.__bv_bitblast_ult.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_ult` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fult.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_ult x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_ult.case_0 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_ult
  unfold EoCases.__bv_bitblast_ult.case_0
  logos_eq

theorem body_eo__24bv_5fbitblast_5fult_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fult s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fult.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fbitblast_5fult
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fbitblast_5fult_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  body_stuck hinv1 hG using hn_a0 hn_a1 hn_a2 hc0 in EoCases.__bv_bitblast_ult.case_0

theorem eo__24bv_5fbitblast_5fult_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fult.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fult
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitblast_5fult s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_ult x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fult_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2 = some (__bv_bitblast_ult_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitblast_5fult_5frec
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_ult_rec.case_0
  case_done hinv2 hG with h_a2 in EoCases.__bv_bitblast_ult_rec.case_0 using hn_a0 hn_a1 hn_a2

theorem case_1_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (Next.Done t)) =>
        ∃ res, EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok (some (Next.Again arr)) =>
        ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2 = some (__bv_bitblast_ult_rec y0 y1 y2)
      | core.result.Result.Ok none => EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fbitblast_5fult_5frec more_0_eo__24bv_5fbitblast_5fult_5frec more_1_eo__24bv_5fbitblast_5fult_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_bitblast_ult_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_bitblast_ult_rec.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_bitblast_ult_rec.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_or.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo_and.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  step as ⟨e_v16, he_v16⟩
  store_step with CtorSpec.eo__3d.construct s4 e_v16 (by rw [he_v16]; exact empty_args) hinv4 h64 as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s5 v16 v5 _ _ hinv5 h64 h_v16 h_v5 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s6 v17 v12 _ _ hinv6 h64 h_v17 h_v12 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with Store.apply_rep s7 v15 v18 _ _ hinv7 h64 h_v15 h_v18 (by ns_tac) (by ns_tac) as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  step as ⟨e_v20, he_v20⟩
  store_step with CtorSpec.eo_and.construct s8 e_v20 (by rw [he_v20]; exact empty_args) hinv8 h64 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  store_step with Store.apply_rep s9 v20 a2 _ _ hinv9 h64 h_v20 h_a2 (by ns_tac) (by ns_tac) as ⟨v21, s10, hinv10, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20
  store_step with Store.literal_boolean_spec s10 true hinv10 h64 as ⟨v22, s11, hinv11, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21
  store_step with Store.apply_rep s11 v21 v22 _ _ hinv11 h64 h_v21 h_v22 (by ns_tac) (by ns_tac) as ⟨v23, s12, hinv12, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22
  store_step with Store.apply_rep s12 v19 v23 _ _ hinv12 h64 h_v19 h_v23 (by ns_tac) (by ns_tac) as ⟨v24, s13, hinv13, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23
  store_step with Store.apply_rep s13 v14 v24 _ _ hinv13 h64 h_v14 h_v24 (by ns_tac) (by ns_tac) as ⟨v25, s14, hinv14, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  step as ⟨e_v26, he_v26⟩
  store_step with CtorSpec.eo_or.construct s14 e_v26 (by rw [he_v26]; exact empty_args) hinv14 h64 as ⟨v26, s15, hinv15, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  step as ⟨e_v27, he_v27⟩
  store_step with CtorSpec.eo_and.construct s15 e_v27 (by rw [he_v27]; exact empty_args) hinv15 h64 as ⟨v27, s16, hinv16, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_not.construct s16 e_v28 (by rw [he_v28]; exact empty_args) hinv16 h64 as ⟨v28, s17, hinv17, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s17 v28 v5 _ _ hinv17 h64 h_v28 h_v5 (by ns_tac) (by ns_tac) as ⟨v29, s18, hinv18, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.apply_rep s18 v27 v29 _ _ hinv18 h64 h_v27 h_v29 (by ns_tac) (by ns_tac) as ⟨v30, s19, hinv19, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  step as ⟨e_v31, he_v31⟩
  store_step with CtorSpec.eo_and.construct s19 e_v31 (by rw [he_v31]; exact empty_args) hinv19 h64 as ⟨v31, s20, hinv20, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s20 v31 v12 _ _ hinv20 h64 h_v31 h_v12 (by ns_tac) (by ns_tac) as ⟨v32, s21, hinv21, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.literal_boolean_spec s21 true hinv21 h64 as ⟨v33, s22, hinv22, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  store_step with Store.apply_rep s22 v32 v33 _ _ hinv22 h64 h_v32 h_v33 (by ns_tac) (by ns_tac) as ⟨v34, s23, hinv23, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  store_step with Store.apply_rep s23 v30 v34 _ _ hinv23 h64 h_v30 h_v34 (by ns_tac) (by ns_tac) as ⟨v35, s24, hinv24, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s24 v26 v35 _ _ hinv24 h64 h_v26 h_v35 (by ns_tac) (by ns_tac) as ⟨v36, s25, hinv25, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  store_step with Store.literal_boolean_spec s25 false hinv25 h64 as ⟨v37, s26, hinv26, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s26 v36 v37 _ _ hinv26 h64 h_v36 h_v37 (by ns_tac) (by ns_tac) as ⟨v38, s27, hinv27, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.apply_rep s27 v25 v38 _ _ hinv27 h64 h_v25 h_v38 (by ns_tac) (by ns_tac) as ⟨v39, s28, hinv28, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  case_again hinv28 hG with h_v2 h_v9 h_v39 in EoCases.__bv_bitblast_ult_rec.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_bitblast_ult_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitblast_5fult_5frec.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_bitblast_ult_rec x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitblast_ult_rec.case_0 x_a0 x_a1 x_a2, EoCases.__bv_bitblast_ult_rec.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitblast_ult_rec
  unfold EoCases.__bv_bitblast_ult_rec.case_0 EoCases.__bv_bitblast_ult_rec.case_1
  logos_eq

theorem step_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    step_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (Next.Done t) => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Ok (Next.Again arr) =>
        s'.budget < s.budget ∧ ∃ (u0 : Term) (y0 : _) (u1 : Term) (y1 : _) (u2 : Term) (y2 : _), arr.val = [u0, u1, u2] ∧ Represents.rep s' u0 y0 ∧ Represents.rep s' u1 y1 ∧ Represents.rep s' u2 y2 ∧
          __bv_bitblast_ult_rec x_a0 x_a1 x_a2 = __bv_bitblast_ult_rec y0 y1 y2
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitblast_5fult_5frec.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold step_eo__24bv_5fbitblast_5fult_5frec
  have hG := Store.Grows.refl s
  tick_step as ⟨s1, hinv1⟩ growing hG carrying h_a0 h_a1 h_a2
  stuck_check h_a0 : x_a0 as hn_a0 else hinv1 hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv1 hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv1 hG
  round_step with case_0_eo__24bv_5fbitblast_5fult_5frec_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2
  round_step with case_1_eo__24bv_5fbitblast_5fult_5frec_spec n ih s2 a0 a1 a2 x_a0 x_a1 x_a2 hinv2 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s3, hinv3, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 hbud using hn_a0 hn_a1 hn_a2 hc0
  round_stuck hinv3 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_bitblast_ult_rec.case_0 EoCases.__bv_bitblast_ult_rec.case_1

theorem body_eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  refine (?_ : ∀ (k : Nat) (a0 a1 a2 : Term) (s : Store) (x_a0 : _) (x_a1 : _) (x_a2 : _), s.budget ≤ k → s.Inv → s.remaining ≤ n →
      Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 → Represents.rep s a2 x_a2 →
      body_eo__24bv_5fbitblast_5fult_5frec s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div) s.budget a0 a1 a2 s x_a0 x_a1 x_a2 le_rfl hinv hrem h_a0 h_a1 h_a2
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ihl a0 a1 a2 s x_a0 x_a1 x_a2 hk hinv hrem h_a0 h_a1 h_a2
  unfold body_eo__24bv_5fbitblast_5fult_5frec body_eo__24bv_5fbitblast_5fult_5frec_loop
  step with step_eo__24bv_5fbitblast_5fult_5frec_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok nx =>
    cases nx with
    | Done value =>
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, hr⟩
    | Again next =>
      obtain ⟨hlt, u0, y0, u1, y1, u2, y2, hnext, hrep0, hrep1, hrep2, heq⟩ := hr
      simp only
      have hlen : next.length = 3 := by simp [Array.length, hnext]
      step as ⟨b0, hb0⟩
      obtain rfl : b0 = u0 := by simp [hb0, hnext]
      step as ⟨b1, hb1⟩
      obtain rfl : b1 = u1 := by simp [hb1, hnext]
      step as ⟨b2, hb2⟩
      obtain rfl : b2 = u2 := by simp [hb2, hnext]
      have hrec := ihl s1.budget (by omega) b0 b1 b2 s1 y0 y1 y2 le_rfl hinv1 (hg1.rem hrem)  hrep0  hrep1  hrep2
      unfold body_eo__24bv_5fbitblast_5fult_5frec at hrec
      apply WP.dspec_mono hrec
      loop_close hg1 heq

theorem eo__24bv_5fbitblast_5fult_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitblast_5fult_5frec.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fbitblast_5fult_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 28#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fbitblast_5fult_5frec s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_bitblast_ult_rec x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_28 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_28 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitblast_5fult_5frec_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fbitwidth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fbitwidth s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_bitwidth.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_bitwidth.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fbitwidth
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_bitwidth.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_BitVec.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_bitwidth.case_0
  case_done hinv1 hG with h_v2 in EoCases.__bv_bitwidth.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__bv_bitwidth` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fbitwidth.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_bitwidth x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_bitwidth.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_bitwidth
  unfold EoCases.__bv_bitwidth.case_0
  logos_eq

theorem body_eo__24bv_5fbitwidth_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fbitwidth s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_bitwidth x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fbitwidth.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fbitwidth
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fbitwidth_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_bitwidth.case_0

theorem eo__24bv_5fbitwidth_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fbitwidth.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fbitwidth
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24bv_5fbitwidth s1 a0) (fun s' t => Represents.rep s' t (__bv_bitwidth x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fbitwidth_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fget_5ffirst_5fconst_5fchild_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fget_5ffirst_5fconst_5fchild s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_get_first_const_child.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_get_first_const_child.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fget_5ffirst_5fconst_5fchild
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_get_first_const_child.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_get_first_const_child.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with Store.builtin_spec_is_bin s e_v6 (by rw [he_v6]; rfl) h_v5 hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  have h_ite_v8 := (show if_0_eo__24bv_5fget_5ffirst_5fconst_5fchild s1 v6 v5 v2 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24bv_5fget_5ffirst_5fconst_5fchild
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_term h_v6 with ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩ | ⟨hx_7, hbv_7⟩
    · ite_branch hbv_7
      ite_done hinv1 hG with (eo_ite_true_rep _ hx_7 h_v5)
    · ite_branch hbv_7
      store_step with ih.eo__24bv_5fget_5ffirst_5fconst_5fchild s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
      ite_done hinv2 hG with (eo_ite_false_rep _ hx_7 h_v7)
    · ite_branch hbv_7
      ite_stuck hinv1 hG with hx_7)
  store_step with h_ite_v8 as ⟨v8, s2, hinv2, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv2 hG with h_v8 in EoCases.__bv_get_first_const_child.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_get_first_const_child` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fget_5ffirst_5fconst_5fchild.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_get_first_const_child x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_get_first_const_child.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_get_first_const_child
  unfold EoCases.__bv_get_first_const_child.case_0
  logos_eq

theorem body_eo__24bv_5fget_5ffirst_5fconst_5fchild_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fget_5ffirst_5fconst_5fchild s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_get_first_const_child x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fget_5ffirst_5fconst_5fchild.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fget_5ffirst_5fconst_5fchild
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fget_5ffirst_5fconst_5fchild_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__bv_get_first_const_child.case_0

theorem eo__24bv_5fget_5ffirst_5fconst_5fchild_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fget_5ffirst_5fconst_5fchild.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fget_5ffirst_5fconst_5fchild
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 33#u32 _ [a0] rfl
    (fun s1 => body_eo__24bv_5fget_5ffirst_5fconst_5fchild s1 a0) (fun s' t => Represents.rep s' t (__bv_get_first_const_child x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_33 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_33 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fget_5ffirst_5fconst_5fchild_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_concat.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_concat.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_concat.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__bv_mk_bitblast_step_concat.case_0 using hn_a0

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_concat.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_concat.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_concat.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_concat.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_concat.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_concat.case_1
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fconcat s1 v2 _ hinv1 h64 (hG.rem hrem) h_v2 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with ih.eo__24bv_5fbitblast_5fconcat s2 v7 v5 _ _ hinv2 h64 (hG.rem hrem) h_v7 h_v5 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  case_done hinv3 hG with h_v8 in EoCases.__bv_mk_bitblast_step_concat.case_1 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitblast_step_concat` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fconcat.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __bv_mk_bitblast_step_concat x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_concat.case_0 x_a0, EoCases.__bv_mk_bitblast_step_concat.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_concat
  unfold EoCases.__bv_mk_bitblast_step_concat.case_0 EoCases.__bv_mk_bitblast_step_concat.case_1
  logos_eq

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_concat x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5fconcat.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__bv_mk_bitblast_step_concat.case_0 EoCases.__bv_mk_bitblast_step_concat.case_1

theorem eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5fconcat.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5fconcat
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 37#u32 _ [a0] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat s1 a0) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_concat x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, y0, hargs, hb0, hr⟩ := ProgramSem.of_37 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_37 ⟨a0, x_a0, rfl, Rep.mono hpre h_a0, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5fconcat_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_eq_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_eq_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec
  have hG := Store.Grows.refl s
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_0
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__bv_mk_bitblast_step_eq_rec.case_0 using hn_a0 hn_a1

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_eq_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_eq_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec more_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  pat_unapply h_a1 as ⟨v8, v9, x_v8, x_v9, h_v8, h_v9, hn_v8, hn_v9⟩ using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  pat_unapply h_v8 as ⟨v11, v12, x_v11, x_v12, h_v11, h_v12, hn_v11, hn_v12⟩ using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  step as ⟨e_v13, he_v13⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v13 (by rw [he_v13]; exact empty_args) hinv1 h64 as ⟨v13, s2, hinv2, h_v13⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12
  pat_same v11 v13 with h_v11 h_v13 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo_and.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13
  step as ⟨e_v15, he_v15⟩
  store_step with CtorSpec.eo__3d.construct s3 e_v15 (by rw [he_v15]; exact empty_args) hinv3 h64 as ⟨v15, s4, hinv4, h_v15⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14
  store_step with Store.apply_rep s4 v15 v5 _ _ hinv4 h64 h_v15 h_v5 (by ns_tac) (by ns_tac) as ⟨v16, s5, hinv5, h_v16⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15
  store_step with Store.apply_rep s5 v16 v12 _ _ hinv5 h64 h_v16 h_v12 (by ns_tac) (by ns_tac) as ⟨v17, s6, hinv6, h_v17⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16
  store_step with Store.apply_rep s6 v14 v17 _ _ hinv6 h64 h_v14 h_v17 (by ns_tac) (by ns_tac) as ⟨v18, s7, hinv7, h_v18⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec s7 v2 v9 _ _ hinv7 h64 (hG.rem hrem) h_v2 h_v9 as ⟨v19, s8, hinv8, h_v19⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18
  store_step with Store.apply_mk_rep s8 v18 v19 _ _ hinv8 h64 h_v18 h_v19 as ⟨v20, s9, hinv9, h_v20⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v8 h_v9 h_v11 h_v12 h_v13 h_v14 h_v15 h_v16 h_v17 h_v18 h_v19
  case_done hinv9 hG with h_v20 in EoCases.__bv_mk_bitblast_step_eq_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5 hn_v8 hn_v9 hn_v11 hn_v12

/-- logos's `__bv_mk_bitblast_step_eq_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_mk_bitblast_step_eq_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_eq_rec.case_0 x_a0 x_a1, EoCases.__bv_mk_bitblast_step_eq_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_eq_rec
  unfold EoCases.__bv_mk_bitblast_step_eq_rec.case_0 EoCases.__bv_mk_bitblast_step_eq_rec.case_1
  logos_eq

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_eq_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_mk_bitblast_step_eq_rec.case_0 EoCases.__bv_mk_bitblast_step_eq_rec.case_1

theorem eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 38#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_eq_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_38 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_38 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5feq_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_ite.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_ite.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite more_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite more_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite more_2_eo__24bv_5fmk_5fbitblast_5fstep_5fite
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same v2 v7 with h_v2 h_v7 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  pat_unapply h_a1 as ⟨v9, v10, x_v9, x_v10, h_v9, h_v10, hn_v9, hn_v10⟩ using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  pat_unapply h_v9 as ⟨v12, v13, x_v12, x_v13, h_v12, h_v13, hn_v12, hn_v13⟩ using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  step as ⟨e_v14, he_v14⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s2 e_v14 (by rw [he_v14]; exact empty_args) hinv2 h64 as ⟨v14, s3, hinv3, h_v14⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13
  pat_same v12 v14 with h_v12 h_v14 using hinv3 else hinv3 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  pat_unapply h_a2 as ⟨v16, v17, x_v16, x_v17, h_v16, h_v17, hn_v16, hn_v17⟩ using hinv3 else hinv3 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  pat_unapply h_v16 as ⟨v19, v20, x_v19, x_v20, h_v19, h_v20, hn_v19, hn_v20⟩ using hinv3 else hinv3 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  step as ⟨e_v21, he_v21⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s3 e_v21 (by rw [he_v21]; exact empty_args) hinv3 h64 as ⟨v21, s4, hinv4, h_v21⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20
  pat_same v19 v21 with h_v19 h_v21 using hinv4 else hinv4 hG in EoCases.__bv_mk_bitblast_step_ite.case_0
  step as ⟨e_v22, he_v22⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s4 e_v22 (by rw [he_v22]; exact empty_args) hinv4 h64 as ⟨v22, s5, hinv5, h_v22⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21
  step as ⟨e_v23, he_v23⟩
  store_step with CtorSpec.eo_and.construct s5 e_v23 (by rw [he_v23]; exact empty_args) hinv5 h64 as ⟨v23, s6, hinv6, h_v23⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22
  step as ⟨e_v24, he_v24⟩
  store_step with CtorSpec.eo_or.construct s6 e_v24 (by rw [he_v24]; exact empty_args) hinv6 h64 as ⟨v24, s7, hinv7, h_v24⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23
  step as ⟨e_v25, he_v25⟩
  store_step with CtorSpec.eo_not.construct s7 e_v25 (by rw [he_v25]; exact empty_args) hinv7 h64 as ⟨v25, s8, hinv8, h_v25⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24
  store_step with Store.apply_rep s8 v25 v5 _ _ hinv8 h64 h_v25 h_v5 (by ns_tac) (by ns_tac) as ⟨v26, s9, hinv9, h_v26⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25
  store_step with Store.apply_rep s9 v24 v26 _ _ hinv9 h64 h_v24 h_v26 (by ns_tac) (by ns_tac) as ⟨v27, s10, hinv10, h_v27⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26
  step as ⟨e_v28, he_v28⟩
  store_step with CtorSpec.eo_or.construct s10 e_v28 (by rw [he_v28]; exact empty_args) hinv10 h64 as ⟨v28, s11, hinv11, h_v28⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27
  store_step with Store.apply_rep s11 v28 v13 _ _ hinv11 h64 h_v28 h_v13 (by ns_tac) (by ns_tac) as ⟨v29, s12, hinv12, h_v29⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28
  store_step with Store.literal_boolean_spec s12 false hinv12 h64 as ⟨v30, s13, hinv13, h_v30⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29
  store_step with Store.apply_rep s13 v29 v30 _ _ hinv13 h64 h_v29 h_v30 (by ns_tac) (by ns_tac) as ⟨v31, s14, hinv14, h_v31⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30
  store_step with Store.apply_rep s14 v27 v31 _ _ hinv14 h64 h_v27 h_v31 (by ns_tac) (by ns_tac) as ⟨v32, s15, hinv15, h_v32⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31
  store_step with Store.apply_rep s15 v23 v32 _ _ hinv15 h64 h_v23 h_v32 (by ns_tac) (by ns_tac) as ⟨v33, s16, hinv16, h_v33⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32
  step as ⟨e_v34, he_v34⟩
  store_step with CtorSpec.eo_and.construct s16 e_v34 (by rw [he_v34]; exact empty_args) hinv16 h64 as ⟨v34, s17, hinv17, h_v34⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33
  step as ⟨e_v35, he_v35⟩
  store_step with CtorSpec.eo_or.construct s17 e_v35 (by rw [he_v35]; exact empty_args) hinv17 h64 as ⟨v35, s18, hinv18, h_v35⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34
  store_step with Store.apply_rep s18 v35 v5 _ _ hinv18 h64 h_v35 h_v5 (by ns_tac) (by ns_tac) as ⟨v36, s19, hinv19, h_v36⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35
  step as ⟨e_v37, he_v37⟩
  store_step with CtorSpec.eo_or.construct s19 e_v37 (by rw [he_v37]; exact empty_args) hinv19 h64 as ⟨v37, s20, hinv20, h_v37⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36
  store_step with Store.apply_rep s20 v37 v20 _ _ hinv20 h64 h_v37 h_v20 (by ns_tac) (by ns_tac) as ⟨v38, s21, hinv21, h_v38⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37
  store_step with Store.literal_boolean_spec s21 false hinv21 h64 as ⟨v39, s22, hinv22, h_v39⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38
  store_step with Store.apply_rep s22 v38 v39 _ _ hinv22 h64 h_v38 h_v39 (by ns_tac) (by ns_tac) as ⟨v40, s23, hinv23, h_v40⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39
  store_step with Store.apply_rep s23 v36 v40 _ _ hinv23 h64 h_v36 h_v40 (by ns_tac) (by ns_tac) as ⟨v41, s24, hinv24, h_v41⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40
  store_step with Store.apply_rep s24 v34 v41 _ _ hinv24 h64 h_v34 h_v41 (by ns_tac) (by ns_tac) as ⟨v42, s25, hinv25, h_v42⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41
  store_step with Store.literal_boolean_spec s25 true hinv25 h64 as ⟨v43, s26, hinv26, h_v43⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42
  store_step with Store.apply_rep s26 v42 v43 _ _ hinv26 h64 h_v42 h_v43 (by ns_tac) (by ns_tac) as ⟨v44, s27, hinv27, h_v44⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43
  store_step with Store.apply_rep s27 v33 v44 _ _ hinv27 h64 h_v33 h_v44 (by ns_tac) (by ns_tac) as ⟨v45, s28, hinv28, h_v45⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44
  store_step with Store.apply_rep s28 v22 v45 _ _ hinv28 h64 h_v22 h_v45 (by ns_tac) (by ns_tac) as ⟨v46, s29, hinv29, h_v46⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45
  step as ⟨e_v47, he_v47⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s29 e_v47 (by rw [he_v47]; exact empty_args) hinv29 h64 as ⟨v47, s30, hinv30, h_v47⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46
  store_step with Store.apply_rep s30 v47 v5 _ _ hinv30 h64 h_v47 h_v5 (by ns_tac) (by ns_tac) as ⟨v48, s31, hinv31, h_v48⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s31 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv31 h64 as ⟨v49, s32, hinv32, h_v49⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48
  store_step with Store.apply_rep s32 v48 v49 _ _ hinv32 h64 h_v48 h_v49 (by ns_tac) (by ns_tac) as ⟨v50, s33, hinv33, h_v50⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fite s33 v50 v10 v17 _ _ _ hinv33 h64 (hG.rem hrem) h_v50 h_v10 h_v17 as ⟨v51, s34, hinv34, h_v51⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50
  store_step with Store.apply_mk_rep s34 v46 v51 _ _ hinv34 h64 h_v46 h_v51 as ⟨v52, s35, hinv35, h_v52⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v9 h_v10 h_v12 h_v13 h_v14 h_v16 h_v17 h_v19 h_v20 h_v21 h_v22 h_v23 h_v24 h_v25 h_v26 h_v27 h_v28 h_v29 h_v30 h_v31 h_v32 h_v33 h_v34 h_v35 h_v36 h_v37 h_v38 h_v39 h_v40 h_v41 h_v42 h_v43 h_v44 h_v45 h_v46 h_v47 h_v48 h_v49 h_v50 h_v51
  case_done hinv35 hG with h_v52 in EoCases.__bv_mk_bitblast_step_ite.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5 hn_v9 hn_v10 hn_v12 hn_v13 hn_v16 hn_v17 hn_v19 hn_v20

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_ite.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_ite.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_ite.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_ite.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_ite.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6
  pat_same v2 v7 with h_v2 h_v7 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_ite.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  pat_same a1 v8 with h_a1 h_v8 using hinv3 else hinv3 hG in EoCases.__bv_mk_bitblast_step_ite.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s3 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv3 h64 as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  pat_same a2 v9 with h_a2 h_v9 using hinv4 else hinv4 hG in EoCases.__bv_mk_bitblast_step_ite.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s4 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv4 h64 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__bv_mk_bitblast_step_ite.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitblast_step_ite` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fite.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __bv_mk_bitblast_step_ite x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_ite.case_0 x_a0 x_a1 x_a2, EoCases.__bv_mk_bitblast_step_ite.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_ite
  unfold EoCases.__bv_mk_bitblast_step_ite.case_0 EoCases.__bv_mk_bitblast_step_ite.case_1
  logos_eq

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5fite s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_ite x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5fite.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fite
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__bv_mk_bitblast_step_ite.case_0 EoCases.__bv_mk_bitblast_step_ite.case_1

theorem eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5fite.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5fite
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 39#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5fite s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_ite x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_39 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_39 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5fite_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_var_rec.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_var_rec.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_var_rec.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo__40_40TypedList_2enil.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_var_rec.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Int.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__bv_mk_bitblast_step_var_rec.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s2 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__bv_mk_bitblast_step_var_rec.case_0 using hn_a0 hn_a1 hn_v1 hn_v2

theorem case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__bv_mk_bitblast_step_var_rec.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__bv_mk_bitblast_step_var_rec.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  have hG := Store.Grows.refl s
  pat_unapply h_a1 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_var_rec.case_1
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__bv_mk_bitblast_step_var_rec.case_1
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__bv_mk_bitblast_step_var_rec.case_1
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  step as ⟨e_v8, he_v8⟩
  store_step with CtorSpec.eo__40bit.construct s2 e_v8 (by rw [he_v8]; rfl) h_v5 hinv2 h64 as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 a0 _ _ hinv3 h64 h_v8 h_a0 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with Store.apply_rep s4 v7 v9 _ _ hinv4 h64 h_v7 h_v9 (by ns_tac) (by ns_tac) as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  store_step with ih.eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s5 a0 v2 _ _ hinv5 h64 (hG.rem hrem) h_a0 h_v2 as ⟨v11, s6, hinv6, h_v11⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10
  store_step with Store.apply_mk_rep s6 v10 v11 _ _ hinv6 h64 h_v10 h_v11 as ⟨v12, s7, hinv7, h_v12⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9 h_v10 h_v11
  case_done hinv7 hG with h_v12 in EoCases.__bv_mk_bitblast_step_var_rec.case_1 using hn_a0 hn_a1 hn_v1 hn_v2 hn_v4 hn_v5

/-- logos's `__bv_mk_bitblast_step_var_rec` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __bv_mk_bitblast_step_var_rec x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__bv_mk_bitblast_step_var_rec.case_0 x_a0 x_a1, EoCases.__bv_mk_bitblast_step_var_rec.case_1 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __bv_mk_bitblast_step_var_rec
  unfold EoCases.__bv_mk_bitblast_step_var_rec.case_0 EoCases.__bv_mk_bitblast_step_var_rec.case_1
  logos_eq

theorem body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__bv_mk_bitblast_step_var_rec x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  case_step with case_0_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1
  case_step with case_1_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hn_a0 hn_a1 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hc0 hc1 in EoCases.__bv_mk_bitblast_step_var_rec.case_0 EoCases.__bv_mk_bitblast_step_var_rec.case_1

theorem eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 45#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec s1 a0 a1) (fun s' t => Represents.rep s' t (__bv_mk_bitblast_step_var_rec x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_45 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_45 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24bv_5fmk_5fbitblast_5fstep_5fvar_5frec_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_arg_list.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_arg_list.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5farg_5flist
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_arg_list.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5, hn_v4, hn_v5⟩ using hinv else hinv hG in EoCases.__dt_arg_list.case_0
  step as ⟨e_v6, he_v6⟩
  store_step with CtorSpec.eo_tuple.construct s e_v6 (by rw [he_v6]; exact empty_args) hinv h64 as ⟨v6, s1, hinv1, h_v6⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5
  pat_same v4 v6 with h_v4 h_v6 using hinv1 else hinv1 hG in EoCases.__dt_arg_list.case_0
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo_tuple.construct s1 e_v7 (by rw [he_v7]; exact empty_args) hinv1 h64 as ⟨v7, s2, hinv2, h_v7⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6
  store_step with Store.apply_rep s2 v7 v5 _ _ hinv2 h64 h_v7 h_v5 (by ns_tac) (by ns_tac) as ⟨v8, s3, hinv3, h_v8⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7
  store_step with Store.apply_rep s3 v8 v2 _ _ hinv3 h64 h_v8 h_v2 (by ns_tac) (by ns_tac) as ⟨v9, s4, hinv4, h_v9⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8
  store_step with ih.eo__24tuple_5farg_5flist s4 v9 _ hinv4 h64 (hG.rem hrem) h_v9 as ⟨v10, s5, hinv5, h_v10⟩ growing hG carrying h_a0 h_v1 h_v2 h_v4 h_v5 h_v6 h_v7 h_v8 h_v9
  case_done hinv5 hG with h_v10 in EoCases.__dt_arg_list.case_0 using hn_a0 hn_v1 hn_v2 hn_v4 hn_v5

theorem case_1_eo__24dt_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_arg_list.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_arg_list.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5farg_5flist
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  store_step with ih.eo__24get_5farg_5flist_5frec s1 a0 v0 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v0 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__dt_arg_list.case_1 using hn_a0

/-- logos's `__dt_arg_list` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5farg_5flist.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __dt_arg_list x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_arg_list.case_0 x_a0, EoCases.__dt_arg_list.case_1 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __dt_arg_list
  unfold EoCases.__dt_arg_list.case_0 EoCases.__dt_arg_list.case_1
  logos_eq

theorem body_eo__24dt_5farg_5flist_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24dt_5farg_5flist s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_arg_list x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5farg_5flist.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24dt_5farg_5flist
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24dt_5farg_5flist_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  case_step with case_1_eo__24dt_5farg_5flist_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0 hn_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hn_a0 hc0
  body_stuck hinv2 hG using hn_a0 hc0 hc1 in EoCases.__dt_arg_list.case_0 EoCases.__dt_arg_list.case_1

theorem eo__24dt_5farg_5flist_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5farg_5flist.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24dt_5farg_5flist
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24dt_5farg_5flist s1 a0) (fun s' t => Represents.rep s' t (__dt_arg_list x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5farg_5flist_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_0_eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24dt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_collapse_updater_rhs.case_0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_u32_spec s 0#u32 (0) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  pat_same a2 v3 with h_a2 h_v3 using hinv1 else hinv1 hG in EoCases.__dt_collapse_updater_rhs.case_0
  store_step with Store.apply_rep s1 v1 a1 _ _ hinv1 h64 h_v1 h_a1 (by ns_tac) (by ns_tac) as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__dt_collapse_updater_rhs.case_0 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

theorem case_1_eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) (hn_a2 : x_a2 ≠ Eo.Term.Stuck) :
    case_1_eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__dt_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__dt_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24dt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__dt_collapse_updater_rhs.case_1
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  store_step with Store.literal_int_neg_u32_spec s 1#u32 (-1) (by scalar_tac) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with Store.builtin_spec_add s1 e_v4 (by rw [he_v4]; rfl) h_a2 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3
  store_step with ih.eo__24dt_5fcollapse_5fupdater_5frhs s2 v1 a1 v4 _ _ _ hinv2 h64 (hG.rem hrem) h_v1 h_a1 h_v4 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4
  store_step with Store.apply_mk_rep s3 v5 v2 _ _ hinv3 h64 h_v5 h_v2 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_v1 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__dt_collapse_updater_rhs.case_1 using hn_a0 hn_a1 hn_a2 hn_v1 hn_v2

/-- logos's `__dt_collapse_updater_rhs` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24dt_5fcollapse_5fupdater_5frhs.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) :
    __dt_collapse_updater_rhs x_a0 x_a1 x_a2 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else if x_a2 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__dt_collapse_updater_rhs.case_0 x_a0 x_a1 x_a2, EoCases.__dt_collapse_updater_rhs.case_1 x_a0 x_a1 x_a2] HasStuck.stuck) := by
  conv => lhs; unfold __dt_collapse_updater_rhs
  unfold EoCases.__dt_collapse_updater_rhs.case_0 EoCases.__dt_collapse_updater_rhs.case_1
  logos_eq

theorem body_eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) :
    body_eo__24dt_5fcollapse_5fupdater_5frhs s a0 a1 a2 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__dt_collapse_updater_rhs x_a0 x_a1 x_a2)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24dt_5fcollapse_5fupdater_5frhs.rust_eq x_a0 x_a1 x_a2 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2)]
  unfold body_eo__24dt_5fcollapse_5fupdater_5frhs
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  stuck_check h_a2 : x_a2 as hn_a2 else hinv hG
  case_step with case_0_eo__24dt_5fcollapse_5fupdater_5frhs_spec n ih s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2
  case_step with case_1_eo__24dt_5fcollapse_5fupdater_5frhs_spec n ih s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 hn_a0 hn_a1 hn_a2
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 using hn_a0 hn_a1 hn_a2 hc0
  body_stuck hinv2 hG using hn_a0 hn_a1 hn_a2 hc0 hc1 in EoCases.__dt_collapse_updater_rhs.case_0 EoCases.__dt_collapse_updater_rhs.case_1

theorem eo__24dt_5fcollapse_5fupdater_5frhs_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24dt_5fcollapse_5fupdater_5frhs.Spec n := by
  intro s a0 a1 a2 x_a0 x_a1 x_a2 hinv h64 hrem h_a0 h_a1 h_a2
  unfold eo__24dt_5fcollapse_5fupdater_5frhs
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 62#u32 _ [a0, a1, a2] rfl
    (fun s1 => body_eo__24dt_5fcollapse_5fupdater_5frhs s1 a0 a1 a2) (fun s' t => Represents.rep s' t (__dt_collapse_updater_rhs x_a0 x_a1 x_a2))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, b2, y0, y1, y2, hargs, hb0, hb1, hb2, hr⟩ := ProgramSem.of_62 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      obtain rfl := Rep.functional hb2 (Represents.congr h_a2 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_62 ⟨a0, a1, a2, x_a0, x_a1, x_a2, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, Rep.mono hpre h_a2, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24dt_5fcollapse_5fupdater_5frhs_spec m (ih m hm) s1 a0 a1 a2 x_a0 x_a1 x_a2 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_0_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_0
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_0 using

theorem case_1_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_1_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_1 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_1 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_1
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_1 using

theorem case_2_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    case_2_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_StateObj_proven.case_2 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_StateObj_proven.case_2 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fso_2eproven.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ else hinv hG in EoCases.__eo_StateObj_proven.case_2
  case_done hinv hG with h_v1 in EoCases.__eo_StateObj_proven.case_2 using

/-- logos's `__eo_StateObj_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fStateObj_5fproven.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_StateObj_proven x_a0 =
      (firstSome [EoCases.__eo_StateObj_proven.case_0 x_a0, EoCases.__eo_StateObj_proven.case_1 x_a0, EoCases.__eo_StateObj_proven.case_2 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_StateObj_proven
  unfold EoCases.__eo_StateObj_proven.case_0 EoCases.__eo_StateObj_proven.case_1 EoCases.__eo_StateObj_proven.case_2
  logos_eq

theorem body_eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fStateObj_5fproven s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_StateObj_proven x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fStateObj_5fproven.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fStateObj_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fStateObj_5fproven_spec n ih s a0 x_a0 hinv h64 hrem h_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using
  case_step with case_1_eo__24eo_5fStateObj_5fproven_spec n ih s1 a0 x_a0 hinv1 h64 (hG.rem hrem) h_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 using hc0
  case_step with case_2_eo__24eo_5fStateObj_5fproven_spec n ih s2 a0 x_a0 hinv2 h64 (hG.rem hrem) h_a0
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_StateObj_proven.case_0 EoCases.__eo_StateObj_proven.case_1 EoCases.__eo_StateObj_proven.case_2

theorem eo__24eo_5fStateObj_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fStateObj_5fproven.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fStateObj_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fStateObj_5fproven s1 a0) (fun s' t => Represents.rep s' t (__eo_StateObj_proven x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fStateObj_5fproven_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fr_2escope.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fal_2enil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0
  pat_same a2 v1 with h_a2 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5findl_2econs.destruct h_a4 as ⟨v3, x_v3, h_v3⟩ ⟨v4, x_v4, h_v4⟩ else hinv2 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5findl_2enil.construct s2 e_v5 (by rw [he_v5]; exact empty_args) hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4
  pat_same v4 v5 with h_v4 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_cmd_step_pop_proven.case_0
  store_step with ih.eo__24eo_5fstate_5fproven_5fnth s3 a0 v3 _ _ hinv3 h64 (hG.rem hrem) h_a0 h_v3 (by good_tac) as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5
  have hn_v6 := state_proven_nth_ne_stuck_of h_v6 (by good_tac)
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24eo_5fpf.construct s4 e_v7 (by rw [he_v7]; rfl) h_v6 hinv4 h64 as ⟨v7, s5, hinv5, h_v7⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6
  store_step with ih.eo__24eo_5fprog_5fscope s5 a3 v7 _ _ hinv5 h64 (hG.rem hrem) h_a3 h_v7 (by good_tac) as ⟨v8, s6, hinv6, h_v8⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 h_v0 h_v1 h_v3 h_v4 h_v5 h_v6 h_v7
  case_done hinv6 hG with h_v8 in EoCases.__eo_cmd_step_pop_proven.case_0 using hn_v6

theorem case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.construct_stuck_spec s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4
  case_done hinv1 hG with h_v0 in EoCases.__eo_cmd_step_pop_proven.case_1 using

/-- logos's `__eo_cmd_step_pop_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fcmd_5fstep_5fpop_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) (hw_a2 : Valid.valid x_a2) (hw_a3 : Valid.valid x_a3) (hw_a4 : Valid.valid x_a4) :
    __eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4 =
      (firstSome [EoCases.__eo_cmd_step_pop_proven.case_0 x_a0 x_a1 x_a2 x_a3 x_a4, EoCases.__eo_cmd_step_pop_proven.case_1 x_a0 x_a1 x_a2 x_a3 x_a4] HasStuck.stuck) := by
  conv => lhs; unfold __eo_cmd_step_pop_proven
  unfold EoCases.__eo_cmd_step_pop_proven.case_0 EoCases.__eo_cmd_step_pop_proven.case_1
  logos_eq

theorem body_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 a2 a3 a4 : Term) (x_a0 : _) (x_a1 : _) (x_a2 : _) (x_a3 : _) (x_a4 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (h_a2 : Represents.rep s a2 x_a2) (h_a3 : Represents.rep s a3 x_a3) (h_a4 : Represents.rep s a4 x_a4) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5fcmd_5fstep_5fpop_5fproven s a0 a1 a2 a3 a4 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fcmd_5fstep_5fpop_5fproven.rust_eq x_a0 x_a1 x_a2 x_a3 x_a4 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1) (by valid_tac hinv h_a2) (by valid_tac hinv h_a3) (by valid_tac hinv h_a4)]
  unfold body_eo__24eo_5fcmd_5fstep_5fpop_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using
  case_step with case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec n ih s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 (hG.rem hrem) h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 h_a2 h_a3 h_a4 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_cmd_step_pop_proven.case_0 EoCases.__eo_cmd_step_pop_proven.case_1

theorem eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fcmd_5fstep_5fpop_5fproven.Spec n := by
  intro s a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv h64 hrem h_a0 h_a1 h_a2 h_a3 h_a4 hg_a0
  unfold eo__24eo_5fcmd_5fstep_5fpop_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fcmd_5fstep_5fpop_5fproven s1 a0 a1 a2 a3 a4) (fun s' t => Represents.rep s' t (__eo_cmd_step_pop_proven x_a0 x_a1 x_a2 x_a3 x_a4))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fcmd_5fstep_5fpop_5fproven_spec m (ih m hm) s1 a0 a1 a2 a3 a4 x_a0 x_a1 x_a2 x_a3 x_a4 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) (by congr_one h_a2 hn) (by congr_one h_a3 hn) (by congr_one h_a4 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_lookup.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_lookup.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedd_2econs.destruct h_a1 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ ⟨v3, x_v3, h_v3⟩ else hinv hG in EoCases.__eo_dd_lookup.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with Store.native_spec_streq s e_v4 (by rw [he_v4]; rfl) h_a0 h_v1 hinv h64 as ⟨v4, s1, hinv1, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  rw [← Bridge.native_streq] at h_v4
  have h_ite_v6 := (show if_0_eo__24eo_5fdd_5flookup s1 v4 v2 a0 v3 ⦃ r s' => s'.Inv ∧ s1.Grows s' ∧ match r with | core.result.Result.Ok t => Represents.rep s' t (SmtEval.native_ite _ _ _) | core.result.Result.Err _ => True ⦄div from by
    unfold if_0_eo__24eo_5fdd_5flookup
    have hrem := (hG.rem hrem)
    have hG := Store.Grows.refl s1
    rcases Store.boolean_value_native h_v4 with ⟨hx_5, hbv_5⟩ | ⟨hx_5, hbv_5⟩
    · ite_branch hbv_5
      ite_done hinv1 hG with (native_ite_true_rep _ hx_5 h_v2)
    · ite_branch hbv_5
      store_step with ih.eo__24eo_5fdd_5flookup s1 a0 v3 _ _ hinv1 h64 (hG.rem hrem) h_a0 h_v3 as ⟨v5, s2, hinv2, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
      ite_done hinv2 hG with (native_ite_false_rep _ hx_5 h_v5))
  store_step with h_ite_v6 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv2 hG with h_v6 in EoCases.__eo_dd_lookup.case_0 using

theorem case_1_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_lookup.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_lookup.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedd_2enil.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a1 v0 with h_a1 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dd_lookup.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dd_lookup.case_1 using

/-- logos's `__eo_dd_lookup` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdd_5flookup.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dd_lookup x_a0 x_a1 =
      (firstSome [EoCases.__eo_dd_lookup.case_0 x_a0 x_a1, EoCases.__eo_dd_lookup.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dd_lookup
  unfold EoCases.__eo_dd_lookup.case_0 EoCases.__eo_dd_lookup.case_1
  logos_eq

theorem body_eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdd_5flookup s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdd_5flookup.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdd_5flookup
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdd_5flookup_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdd_5flookup_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_dd_lookup.case_0 EoCases.__eo_dd_lookup.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fdd_5flookup_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdd_5flookup.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdd_5flookup
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 76#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdd_5flookup s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dd_lookup x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_76 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_76 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdd_5flookup_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dd_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dd_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdd_5fresolve
  have hG := Store.Grows.refl s
  store_step with ih.eo__24eo_5fdd_5flookup s a0 a1 _ _ hinv h64 hrem h_a0 h_a1 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  store_step with ih.eo__24eo_5fdt_5fresolve s1 v0 a1 _ _ hinv1 h64 (hG.rem hrem) h_v0 h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dd_resolve.case_0 using

/-- logos's `__eo_dd_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdd_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dd_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dd_resolve.case_0 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dd_resolve
  unfold EoCases.__eo_dd_resolve.case_0
  logos_eq

theorem body_eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdd_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdd_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdd_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdd_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  body_stuck hinv1 hG using hc0 in EoCases.__eo_dd_resolve.case_0 splitting x_a0 x_a1

theorem eo__24eo_5fdd_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdd_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdd_5fresolve
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdd_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dd_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdd_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_disamb_type_seq_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_disamb_type_seq_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_disamb_type_seq_empty.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Seq.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_disamb_type_seq_empty.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Seq.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_disamb_type_seq_empty.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_disamb_type_seq_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdisamb_5ftype_5fseq_2eempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_disamb_type_seq_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_disamb_type_seq_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_disamb_type_seq_empty
  unfold EoCases.__eo_disamb_type_seq_empty.case_0
  logos_eq

theorem body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_disamb_type_seq_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdisamb_5ftype_5fseq_2eempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_disamb_type_seq_empty.case_0

theorem eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdisamb_5ftype_5fseq_2eempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdisamb_5ftype_5fseq_2eempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty s1 a0) (fun s' t => Represents.rep s' t (__eo_disamb_type_seq_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdisamb_5ftype_5fseq_2eempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_disamb_type_set_empty.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_disamb_type_set_empty.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2, hn_v1, hn_v2⟩ using hinv else hinv hG in EoCases.__eo_disamb_type_set_empty.case_0
  step as ⟨e_v3, he_v3⟩
  store_step with CtorSpec.eo_Set.construct s e_v3 (by rw [he_v3]; exact empty_args) hinv h64 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_v1 h_v2
  pat_same v1 v3 with h_v1 h_v3 using hinv1 else hinv1 hG in EoCases.__eo_disamb_type_set_empty.case_0
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_Set.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3
  store_step with Store.apply_rep s2 v4 v2 _ _ hinv2 h64 h_v4 h_v2 (by ns_tac) (by ns_tac) as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_disamb_type_set_empty.case_0 using hn_a0 hn_v1 hn_v2

/-- logos's `__eo_disamb_type_set_empty` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdisamb_5ftype_5fset_2eempty.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_disamb_type_set_empty x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_disamb_type_set_empty.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_disamb_type_set_empty
  unfold EoCases.__eo_disamb_type_set_empty.case_0
  logos_eq

theorem body_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fdisamb_5ftype_5fset_2eempty s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_disamb_type_set_empty x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdisamb_5ftype_5fset_2eempty.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fdisamb_5ftype_5fset_2eempty
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_disamb_type_set_empty.case_0

theorem eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdisamb_5ftype_5fset_2eempty.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fdisamb_5ftype_5fset_2eempty
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fdisamb_5ftype_5fset_2eempty s1 a0) (fun s' t => Represents.rep s' t (__eo_disamb_type_set_empty x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdisamb_5ftype_5fset_2eempty_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedt_2esum.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dt_resolve.case_0
  store_step with ih.eo__24eo_5fdtc_5fresolve s v1 a1 _ _ hinv h64 hrem h_v1 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  store_step with ih.eo__24eo_5fdt_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fedt_2esum.construct s2 e_v5 (by rw [he_v5]; rfl) h_v3 h_v4 hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3 h_v4
  case_done hinv3 hG with h_v5 in EoCases.__eo_dt_resolve.case_0 using

theorem case_1_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dt_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dt_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dt_resolve.case_1
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedt_2enull.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dt_resolve.case_1 using

/-- logos's `__eo_dt_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdt_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dt_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dt_resolve.case_0 x_a0 x_a1, EoCases.__eo_dt_resolve.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dt_resolve
  unfold EoCases.__eo_dt_resolve.case_0 EoCases.__eo_dt_resolve.case_1
  logos_eq

theorem body_eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdt_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdt_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdt_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdt_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdt_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_dt_resolve.case_0 EoCases.__eo_dt_resolve.case_1 splitting x_a0 x_a1

theorem eo__24eo_5fdt_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdt_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdt_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 82#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdt_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dt_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_82 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_82 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdt_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_0_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_0
  pat_destruct CtorSpec.eo__24emb_5fDatatypeTypeRef.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with CtorSpec.eo__24emb_5fDatatypeType.construct s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fdtc_5fresolve s1 v2 a1 _ _ hinv1 h64 (hG.rem hrem) h_v2 h_a1 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  step as ⟨e_v7, he_v7⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2econs.construct s2 e_v7 (by rw [he_v7]; rfl) h_v5 h_v6 hinv2 h64 as ⟨v7, s3, hinv3, h_v7⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5 h_v6
  case_done hinv3 hG with h_v7 in EoCases.__eo_dtc_resolve.case_0 using

theorem case_1_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_1_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fedtc_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_dtc_resolve.case_1
  store_step with ih.eo__24eo_5fdtc_5fresolve s v2 a1 _ _ hinv h64 hrem h_v2 h_a1 as ⟨v3, s1, hinv1, h_v3⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2econs.construct s1 e_v4 (by rw [he_v4]; rfl) h_v1 h_v3 hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v3
  case_done hinv2 hG with h_v4 in EoCases.__eo_dtc_resolve.case_1 using

theorem case_2_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    case_2_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_dtc_resolve.case_2
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24emb_5fedtc_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_dtc_resolve.case_2 using

/-- logos's `__eo_dtc_resolve` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fdtc_5fresolve.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_dtc_resolve x_a0 x_a1 =
      (firstSome [EoCases.__eo_dtc_resolve.case_0 x_a0 x_a1, EoCases.__eo_dtc_resolve.case_1 x_a0 x_a1, EoCases.__eo_dtc_resolve.case_2 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_dtc_resolve
  unfold EoCases.__eo_dtc_resolve.case_0 EoCases.__eo_dtc_resolve.case_1 EoCases.__eo_dtc_resolve.case_2
  logos_eq

theorem body_eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fdtc_5fresolve s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fdtc_5fresolve.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fdtc_5fresolve
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5fdtc_5fresolve_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5fdtc_5fresolve_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  case_step with case_2_eo__24eo_5fdtc_5fresolve_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1 using hc0 hc1
  body_stuck hinv3 hG using hc0 hc1 hc2 in EoCases.__eo_dtc_resolve.case_0 EoCases.__eo_dtc_resolve.case_1 EoCases.__eo_dtc_resolve.case_2 splitting x_a0 x_a1

theorem eo__24eo_5fdtc_5fresolve_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fdtc_5fresolve.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fdtc_5fresolve
  apply WP.dspec_mono (Store.framed_cached s hinv hrem 85#u32 _ [a0, a1] rfl
    (fun s1 => body_eo__24eo_5fdtc_5fresolve s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_dtc_resolve x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (by
      intro s1 res hn hsem
      obtain ⟨b0, b1, y0, y1, hargs, hb0, hb1, hr⟩ := ProgramSem.of_85 hsem
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain rfl := Rep.functional hb0 (Represents.congr h_a0 hn)
      obtain rfl := Rep.functional hb1 (Represents.congr h_a1 hn)
      exact hr)
    (by
      intro s1 res hpre h
      exact ProgramSem.to_85 ⟨a0, a1, x_a0, x_a1, rfl, Rep.mono hpre h_a0, Rep.mono hpre h_a1, h⟩)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fdtc_5fresolve_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  pat_destruct CtorSpec.eo__24emb_5fs_2econs.destruct h_a0 as ⟨v1, x_v1, h_v1⟩ ⟨v2, x_v2, h_v2⟩ else hinv hG in EoCases.__eo_invoke_cmd_check_proven.case_0
  pat_destruct CtorSpec.eo__24emb_5fso_2eproven.destruct h_v1 as ⟨v4, x_v4, h_v4⟩ else hinv hG in EoCases.__eo_invoke_cmd_check_proven.case_0
  step as ⟨e_v5, he_v5⟩
  store_step with Store.builtin_spec_eq s e_v5 (by rw [he_v5]; rfl) h_v4 h_a1 hinv h64 as ⟨v5, s1, hinv1, h_v5⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4
  store_step with ih.eo__24eo_5fpush_5fproven_5fcheck s1 v5 v4 v2 _ _ _ hinv1 h64 (hG.rem hrem) h_v5 h_v4 h_v2 (by good_tac) as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_a0 h_a1 h_v1 h_v2 h_v4 h_v5
  case_done hinv2 hG with h_v6 in EoCases.__eo_invoke_cmd_check_proven.case_0 using

theorem case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24emb_5fs_2eStuck.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_invoke_cmd_check_proven.case_1 using

/-- logos's `__eo_invoke_cmd_check_proven` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_invoke_cmd_check_proven x_a0 x_a1 =
      (firstSome [EoCases.__eo_invoke_cmd_check_proven.case_0 x_a0 x_a1, EoCases.__eo_invoke_cmd_check_proven.case_1 x_a0 x_a1] default) := by
  conv => lhs; unfold __eo_invoke_cmd_check_proven
  unfold EoCases.__eo_invoke_cmd_check_proven.case_0 EoCases.__eo_invoke_cmd_check_proven.case_1
  logos_eq

theorem body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hg_a0 : StateOK x_a0) :
    body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  have hG := Store.Grows.refl s
  case_step with case_0_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1 using
  case_step with case_1_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hg_a0
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1 using hc0
  body_stuck hinv2 hG using hc0 hc1 in EoCases.__eo_invoke_cmd_check_proven.case_0 EoCases.__eo_invoke_cmd_check_proven.case_1 splitting x_a0 x_a1

theorem eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5finvoke_5fcmd_5fcheck_5fproven.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hg_a0
  unfold eo__24eo_5finvoke_5fcmd_5fcheck_5fproven
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_invoke_cmd_check_proven x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5finvoke_5fcmd_5fcheck_5fproven_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn) hg_a0))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40TypedList_2econs.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_0
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5f_40_40TypedList_2econs s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_0 using hn_a0 hn_a1

theorem case_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_or.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_1
  store_step with Store.literal_boolean_spec s1 false hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_1
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_1 using hn_a0 hn_a1

theorem case_2_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_2_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_2_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_and.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_2
  store_step with Store.literal_boolean_spec s1 true hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_2
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_2 using hn_a0 hn_a1

theorem case_3_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_3_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_3_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_3
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5f_2b s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_3 using hn_a0 hn_a1

theorem case_4_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_4_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_4_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__2a.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_4
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5f_2a s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_4 using hn_a0 hn_a1

theorem case_5_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_5_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_5_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_concat.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_5
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_5
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_5 using hn_a0 hn_a1

theorem case_6_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_6_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_6_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvand.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_6
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvand s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_6 using hn_a0 hn_a1

theorem case_7_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_7_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_7_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_7
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvor s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_7 using hn_a0 hn_a1

theorem case_8_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_8_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_8_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvxor.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_8
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvxor s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_8 using hn_a0 hn_a1

theorem case_9_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_9_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_9_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvadd.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_9
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvadd s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_9 using hn_a0 hn_a1

theorem case_10_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_10_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_10_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_bvmul.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_10
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fbvmul s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_10 using hn_a0 hn_a1

theorem case_11_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_11_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_11_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40from_5fbools.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_11
  try simp only [num.Integer.from_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
  store_step with Store.literal_binary_u32_spec s1 0#u32 0#u32 (0) (0) rfl rfl (by unfold Tree.okBv; norm_num) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_11
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_11 using hn_a0 hn_a1

theorem case_12_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_12_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_12_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_str_2e_2b_2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_12
  store_step with ih.eo__24eo_5fis_5flist_5fnil_5fstr_2e_2b_2b s1 a1 _ hinv1 h64 (hG.rem hrem) h_a1 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  case_done hinv2 hG with h_v1 in EoCases.__eo_is_list_nil.case_12 using hn_a0 hn_a1

theorem case_13_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_13_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_13_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2e_2b_2b.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_13
  pat_unapply h_a1 as ⟨v2, v3, x_v2, x_v3, h_v2, h_v3, hn_v2, hn_v3⟩ using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_13
  step as ⟨e_v4, he_v4⟩
  store_step with CtorSpec.eo_str_2eto_5fre.construct s1 e_v4 (by rw [he_v4]; exact empty_args) hinv1 h64 as ⟨v4, s2, hinv2, h_v4⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3
  pat_same v2 v4 with h_v2 h_v4 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_13
  try simp only [eostring.EoString.from_code_points, Std.bind_ok]
  store_step with Store.literal_str_vec_spec s2 _ _ rfl hinv2 h64 as ⟨v5, s3, hinv3, h_v5⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v4
  pat_same v3 v5 with h_v3 h_v5 using hinv3 else hinv3 hG in EoCases.__eo_is_list_nil.case_13
  store_step with Store.literal_boolean_spec s3 true hinv3 h64 as ⟨v6, s4, hinv4, h_v6⟩ growing hG carrying h_a0 h_a1 h_v0 h_v2 h_v3 h_v4 h_v5
  case_done hinv4 hG with h_v6 in EoCases.__eo_is_list_nil.case_13 using hn_a0 hn_a1 hn_v2 hn_v3

theorem case_14_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_14_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_14_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2einter.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_14
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2eall.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_14
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_14 using hn_a0 hn_a1

theorem case_15_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_15_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_15_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_re_2eunion.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_15
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_re_2enone.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_15
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_15 using hn_a0 hn_a1

theorem case_16_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_16_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_16_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_Tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_16
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_UnitTuple.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_16
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_16 using hn_a0 hn_a1

theorem case_17_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_17_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_17_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo_tuple.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_17
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo_tuple_2eunit.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_17
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_17 using hn_a0 hn_a1

theorem case_18_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_18_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_18_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__40_40poly.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_18
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__40_40poly_2ezero.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_18
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_18 using hn_a0 hn_a1

theorem case_19_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_19_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_19_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with CtorSpec.eo__24eo_5fList_5fcons.construct s e_v0 (by rw [he_v0]; exact empty_args) hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  pat_same a0 v0 with h_a0 h_v0 using hinv1 else hinv1 hG in EoCases.__eo_is_list_nil.case_19
  step as ⟨e_v1, he_v1⟩
  store_step with CtorSpec.eo__24eo_5fList_5fnil.construct s1 e_v1 (by rw [he_v1]; exact empty_args) hinv1 h64 as ⟨v1, s2, hinv2, h_v1⟩ growing hG carrying h_a0 h_a1 h_v0
  pat_same a1 v1 with h_a1 h_v1 using hinv2 else hinv2 hG in EoCases.__eo_is_list_nil.case_19
  store_step with Store.literal_boolean_spec s2 true hinv2 h64 as ⟨v2, s3, hinv3, h_v2⟩ growing hG carrying h_a0 h_a1 h_v0 h_v1
  case_done hinv3 hG with h_v2 in EoCases.__eo_is_list_nil.case_19 using hn_a0 hn_a1

theorem case_20_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    case_20_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_20_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  store_step with Store.literal_boolean_spec s false hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0 h_a1
  case_done hinv1 hG with h_v0 in EoCases.__eo_is_list_nil.case_20 using hn_a0 hn_a1

theorem cases_0_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0⟩ using hn_a0 hn_a1
  group_step with case_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_1 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_1⟩ using hn_a0 hn_a1 hl_0
  group_step with case_2_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_2 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] from rfl)
    otherwise ⟨hl_2⟩ using hn_a0 hn_a1 hl_0 hl_1
  group_step with case_3_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_3⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3⟩

theorem cases_0_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_4_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] from rfl)
    otherwise ⟨hl_4⟩ using hn_a0 hn_a1
  group_step with case_5_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_5 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] from rfl)
    otherwise ⟨hl_5⟩ using hn_a0 hn_a1 hl_4
  group_step with case_6_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_6 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] from rfl)
    otherwise ⟨hl_6⟩ using hn_a0 hn_a1 hl_4 hl_5
  group_step with case_7_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_7⟩ using hn_a0 hn_a1 hl_4 hl_5 hl_6
  group_none hinv4 hG with ⟨hl_4, hl_5, hl_6, hl_7⟩

theorem cases_0_2_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_2_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_2_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_8_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] from rfl)
    otherwise ⟨hl_8⟩ using hn_a0 hn_a1
  group_step with case_9_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_9 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] from rfl)
    otherwise ⟨hl_9⟩ using hn_a0 hn_a1 hl_8
  group_step with case_10_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_10 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] from rfl)
    otherwise ⟨hl_10⟩ using hn_a0 hn_a1 hl_8 hl_9
  group_step with case_11_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_11⟩ using hn_a0 hn_a1 hl_8 hl_9 hl_10
  group_none hinv4 hG with ⟨hl_8, hl_9, hl_10, hl_11⟩

theorem cases_0_3_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_3_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_3_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_12_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_12⟩ using hn_a0 hn_a1
  group_step with case_13_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_13 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_13⟩ using hn_a0 hn_a1 hl_12
  group_step with case_14_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_14 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_14⟩ using hn_a0 hn_a1 hl_12 hl_13
  group_step with case_15_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_15⟩ using hn_a0 hn_a1 hl_12 hl_13 hl_14
  group_none hinv4 hG with ⟨hl_12, hl_13, hl_14, hl_15⟩

theorem cases_0_4_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_4_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_4_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_16_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] from rfl)
    otherwise ⟨hl_16⟩ using hn_a0 hn_a1
  group_step with case_17_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_17 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] from rfl)
    otherwise ⟨hl_17⟩ using hn_a0 hn_a1 hl_16
  group_step with case_18_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_18 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] from rfl)
    otherwise ⟨hl_18⟩ using hn_a0 hn_a1 hl_16 hl_17
  group_step with case_19_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_19⟩ using hn_a0 hn_a1 hl_16 hl_17 hl_18
  group_none hinv4 hG with ⟨hl_16, hl_17, hl_18, hl_19⟩

theorem cases_0_5_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_0_5_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_0_5_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with case_20_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_20⟩ using hn_a0 hn_a1
  group_none hinv1 hG with hl_20

theorem cases_1_0_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_1_0_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_0 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_1 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_2 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_3 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_4 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_5 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_6 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_7 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_8 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_9 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_10 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_11 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_12 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_13 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_14 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_15 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_0_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with cases_0_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3⟩ using hn_a0 hn_a1
  group_step with cases_0_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_4, hl_5, hl_6, hl_7⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3
  group_step with cases_0_2_eo__24eo_5fis_5flist_5fnil_spec n ih s2 a0 a1 x_a0 x_a1 hinv2 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s3, hinv3, hc2⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] from rfl)
    otherwise ⟨hl_8, hl_9, hl_10, hl_11⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7
  group_step with cases_0_3_eo__24eo_5fis_5flist_5fnil_spec n ih s3 a0 a1 x_a0 x_a1 hinv3 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s4, hinv4, hc3⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11
  group_none hinv4 hG with ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩

theorem cases_1_1_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) (hn_a1 : x_a1 ≠ Eo.Term.Stuck) :
    cases_1_1_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, (∀ d, firstSome [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] d = res) ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil.case_16 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_17 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_18 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_19 x_a0 x_a1 = none ∧ EoCases.__eo_is_list_nil.case_20 x_a0 x_a1 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold cases_1_1_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  group_step with cases_0_4_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19⟩ using hn_a0 hn_a1
  group_step with cases_0_5_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_20⟩ using hn_a0 hn_a1 hl_16 hl_17 hl_18 hl_19
  group_none hinv2 hG with ⟨hl_16, hl_17, hl_18, hl_19, hl_20⟩

/-- logos's `__eo_is_list_nil` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil.rust_eq (x_a0 : _) (x_a1 : _) (hw_a0 : Valid.valid x_a0) (hw_a1 : Valid.valid x_a1) :
    __eo_is_list_nil x_a0 x_a1 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else if x_a1 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil
  unfold EoCases.__eo_is_list_nil.case_0 EoCases.__eo_is_list_nil.case_1 EoCases.__eo_is_list_nil.case_2 EoCases.__eo_is_list_nil.case_3 EoCases.__eo_is_list_nil.case_4 EoCases.__eo_is_list_nil.case_5 EoCases.__eo_is_list_nil.case_6 EoCases.__eo_is_list_nil.case_7 EoCases.__eo_is_list_nil.case_8 EoCases.__eo_is_list_nil.case_9 EoCases.__eo_is_list_nil.case_10 EoCases.__eo_is_list_nil.case_11 EoCases.__eo_is_list_nil.case_12 EoCases.__eo_is_list_nil.case_13 EoCases.__eo_is_list_nil.case_14 EoCases.__eo_is_list_nil.case_15 EoCases.__eo_is_list_nil.case_16 EoCases.__eo_is_list_nil.case_17 EoCases.__eo_is_list_nil.case_18 EoCases.__eo_is_list_nil.case_19 EoCases.__eo_is_list_nil.case_20
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : Specs n) (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (h_a1 : Represents.rep s a1 x_a1) :
    body_eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil.rust_eq x_a0 x_a1 (by valid_tac hinv h_a0) (by valid_tac hinv h_a1)]
  unfold body_eo__24eo_5fis_5flist_5fnil
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  stuck_check h_a1 : x_a1 as hn_a1 else hinv hG
  body_group_step with cases_1_0_eo__24eo_5fis_5flist_5fnil_spec n ih s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1 hn_a0 hn_a1
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [] ++ [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] from rfl)
    otherwise ⟨hl_0, hl_1, hl_2, hl_3, hl_4, hl_5, hl_6, hl_7, hl_8, hl_9, hl_10, hl_11, hl_12, hl_13, hl_14, hl_15⟩ using hn_a0 hn_a1
  body_group_step with cases_1_1_eo__24eo_5fis_5flist_5fnil_spec n ih s1 a0 a1 x_a0 x_a1 hinv1 h64 (hG.rem hrem) h_a0 h_a1 hn_a0 hn_a1
    as ⟨s2, hinv2, hc1⟩ growing hG carrying h_a0 h_a1
    split (show [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1, EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] = [EoCases.__eo_is_list_nil.case_0 x_a0 x_a1, EoCases.__eo_is_list_nil.case_1 x_a0 x_a1, EoCases.__eo_is_list_nil.case_2 x_a0 x_a1, EoCases.__eo_is_list_nil.case_3 x_a0 x_a1, EoCases.__eo_is_list_nil.case_4 x_a0 x_a1, EoCases.__eo_is_list_nil.case_5 x_a0 x_a1, EoCases.__eo_is_list_nil.case_6 x_a0 x_a1, EoCases.__eo_is_list_nil.case_7 x_a0 x_a1, EoCases.__eo_is_list_nil.case_8 x_a0 x_a1, EoCases.__eo_is_list_nil.case_9 x_a0 x_a1, EoCases.__eo_is_list_nil.case_10 x_a0 x_a1, EoCases.__eo_is_list_nil.case_11 x_a0 x_a1, EoCases.__eo_is_list_nil.case_12 x_a0 x_a1, EoCases.__eo_is_list_nil.case_13 x_a0 x_a1, EoCases.__eo_is_list_nil.case_14 x_a0 x_a1, EoCases.__eo_is_list_nil.case_15 x_a0 x_a1] ++ [EoCases.__eo_is_list_nil.case_16 x_a0 x_a1, EoCases.__eo_is_list_nil.case_17 x_a0 x_a1, EoCases.__eo_is_list_nil.case_18 x_a0 x_a1, EoCases.__eo_is_list_nil.case_19 x_a0 x_a1, EoCases.__eo_is_list_nil.case_20 x_a0 x_a1] ++ [] from rfl)
    otherwise ⟨hl_16, hl_17, hl_18, hl_19, hl_20⟩ using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15
  body_stuck hinv2 hG using hn_a0 hn_a1 hl_0 hl_1 hl_2 hl_3 hl_4 hl_5 hl_6 hl_7 hl_8 hl_9 hl_10 hl_11 hl_12 hl_13 hl_14 hl_15 hl_16 hl_17 hl_18 hl_19 hl_20 in EoCases.__eo_is_list_nil.case_0 EoCases.__eo_is_list_nil.case_1 EoCases.__eo_is_list_nil.case_2 EoCases.__eo_is_list_nil.case_3 EoCases.__eo_is_list_nil.case_4 EoCases.__eo_is_list_nil.case_5 EoCases.__eo_is_list_nil.case_6 EoCases.__eo_is_list_nil.case_7 EoCases.__eo_is_list_nil.case_8 EoCases.__eo_is_list_nil.case_9 EoCases.__eo_is_list_nil.case_10 EoCases.__eo_is_list_nil.case_11 EoCases.__eo_is_list_nil.case_12 EoCases.__eo_is_list_nil.case_13 EoCases.__eo_is_list_nil.case_14 EoCases.__eo_is_list_nil.case_15 EoCases.__eo_is_list_nil.case_16 EoCases.__eo_is_list_nil.case_17 EoCases.__eo_is_list_nil.case_18 EoCases.__eo_is_list_nil.case_19 EoCases.__eo_is_list_nil.case_20

theorem eo__24eo_5fis_5flist_5fnil_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil.Spec n := by
  intro s a0 a1 x_a0 x_a1 hinv h64 hrem h_a0 h_a1
  unfold eo__24eo_5fis_5flist_5fnil
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil s1 a0 a1) (fun s' t => Represents.rep s' t (__eo_is_list_nil x_a0 x_a1))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_spec m (ih m hm) s1 a0 a1 x_a0 x_a1 hinv1 h64 hrem1 (by congr_one h_a0 hn) (by congr_one h_a1 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5f_2a_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5f_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_mult.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_mult.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5f_2a
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_q s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v0
  replace h_v2 := Represents.rep_of_eq h_v2 (y := Eo.Term.Rational (SmtEval.native_mk_rational (1) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_is_eq s2 e_v3 (by rw [he_v3]; rfl) h_v0 h_v2 hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_is_list_nil_mult.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_mult` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5f_2a.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_mult x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_mult.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_mult
  unfold EoCases.__eo_is_list_nil_mult.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5f_2a_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5f_2a s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_mult x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5f_2a.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5f_2a
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5f_2a_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_mult.case_0

theorem eo__24eo_5fis_5flist_5fnil_5f_2a_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5f_2a.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5f_2a
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5f_2a s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_mult x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5f_2a_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

theorem case_0_eo__24eo_5fis_5flist_5fnil_5f_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) (hn_a0 : x_a0 ≠ Eo.Term.Stuck) :
    case_0_eo__24eo_5fis_5flist_5fnil_5f_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__eo_is_list_nil_plus.case_0 x_a0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__eo_is_list_nil_plus.case_0 x_a0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold case_0_eo__24eo_5fis_5flist_5fnil_5f_2b
  have hG := Store.Grows.refl s
  step as ⟨e_v0, he_v0⟩
  store_step with Store.builtin_spec_to_q s e_v0 (by rw [he_v0]; rfl) h_a0 hinv h64 as ⟨v0, s1, hinv1, h_v0⟩ growing hG carrying h_a0
  try simp only [num.Integer.from_u32_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, num.Rational.from_integers_spec, Std.bind_ok]
  try rw [if_neg (by simp)]
  store_step with Store.literal_rational_spec s1 _ hinv1 h64 as ⟨v2, s2, hinv2, h_v2⟩ growing hG carrying h_a0 h_v0
  replace h_v2 := Represents.rep_of_eq h_v2 (y := Eo.Term.Rational (SmtEval.native_mk_rational (0) (1))) (by simp [SmtEval.native_mk_rational])
  step as ⟨e_v3, he_v3⟩
  store_step with Store.builtin_spec_is_eq s2 e_v3 (by rw [he_v3]; rfl) h_v0 h_v2 hinv2 h64 as ⟨v3, s3, hinv3, h_v3⟩ growing hG carrying h_a0 h_v0 h_v2
  case_done hinv3 hG with h_v3 in EoCases.__eo_is_list_nil_plus.case_0 using hn_a0

/-- logos's `__eo_is_list_nil_plus` is what the generated body does: the tests for the stuck term,
then the first case that answers. -/
theorem eo__24eo_5fis_5flist_5fnil_5f_2b.rust_eq (x_a0 : _) (hw_a0 : Valid.valid x_a0) :
    __eo_is_list_nil_plus x_a0 =
      (if x_a0 = Eo.Term.Stuck then HasStuck.stuck else firstSome [EoCases.__eo_is_list_nil_plus.case_0 x_a0] HasStuck.stuck) := by
  conv => lhs; unfold __eo_is_list_nil_plus
  unfold EoCases.__eo_is_list_nil_plus.case_0
  logos_eq

theorem body_eo__24eo_5fis_5flist_5fnil_5f_2b_spec (n : Nat) (ih : Specs n) (s : Store) (a0 : Term) (x_a0 : _)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n) (h_a0 : Represents.rep s a0 x_a0) :
    body_eo__24eo_5fis_5flist_5fnil_5f_2b s a0 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (__eo_is_list_nil_plus x_a0)
      | core.result.Result.Err _ => True ⦄div := by
  rw [eo__24eo_5fis_5flist_5fnil_5f_2b.rust_eq x_a0 (by valid_tac hinv h_a0)]
  unfold body_eo__24eo_5fis_5flist_5fnil_5f_2b
  have hG := Store.Grows.refl s
  stuck_check h_a0 : x_a0 as hn_a0 else hinv hG
  case_step with case_0_eo__24eo_5fis_5flist_5fnil_5f_2b_spec n ih s a0 x_a0 hinv h64 hrem h_a0 hn_a0
    as ⟨s1, hinv1, hc0⟩ growing hG carrying h_a0 using hn_a0
  body_stuck hinv1 hG using hn_a0 hc0 in EoCases.__eo_is_list_nil_plus.case_0

theorem eo__24eo_5fis_5flist_5fnil_5f_2b_spec (n : Nat) (ih : ∀ m < n, Specs m) : eo__24eo_5fis_5flist_5fnil_5f_2b.Spec n := by
  intro s a0 x_a0 hinv h64 hrem h_a0
  unfold eo__24eo_5fis_5flist_5fnil_5f_2b
  apply WP.dspec_mono (Store.framed s hinv hrem
    (fun s1 => body_eo__24eo_5fis_5flist_5fnil_5f_2b s1 a0) (fun s' t => Represents.rep s' t (__eo_is_list_nil_plus x_a0))
    (by intro _ _ _ hn h; congr_one h hn)
    (fun s1 m hinv1 hn hm hrem1 => by
      spec_exact body_eo__24eo_5fis_5flist_5fnil_5f_2b_spec m (ih m hm) s1 a0 x_a0 hinv1 h64 hrem1 (by congr_one h_a0 hn)))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
