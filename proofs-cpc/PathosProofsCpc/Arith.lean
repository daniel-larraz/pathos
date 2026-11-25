module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Runtime.Builtins
public import PathosProofs.Runtime.Strings

/-!
# CPC's arithmetic (CPC only; milestone 7)

The runtime's rational operations are computed from a numerator and a
denominator (`lit.rat_add` and the others, Ethos's runtime-arith-proved):
proved here from the specs of `Rational.from_integers`, `numerator`,
`denominator` and the integer operations, which are all they trust. CPC
only, as CpcMini's logos has none of the builtins they serve (`eo::add`, …),
and so that CpcMini's proofs rest on no more than they did.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `rat n d`: the rational `n / d`, for `d` not zero. -/
theorem lit_rat_spec (n d : num.Integer) (hd : d.toInt ≠ 0) :
    lit.rat n d = ok (num.Rational.ofRat ((n.toInt : ℚ) / (d.toInt : ℚ))) := by
  unfold lit.rat
  rw [num.Rational.from_integers_spec]
  simp [hd]

theorem rat_den_ne (q : ℚ) : ((q.den : Int) : ℚ) ≠ 0 := by
  exact_mod_cast q.den_nz

theorem lit_rat_add_spec (a b : num.Rational) :
    lit.rat_add a b = ok (num.Rational.ofRat (a.toRat + b.toRat)) := by
  unfold lit.rat_add
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.mul_spec,
    num.Integer.add_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  rw [lit_rat_spec _ _ (by simp [num.Integer.toInt_ofInt])]
  congr 2
  simp only [num.Integer.toInt_ofInt]
  push_cast
  conv => rhs; rw [← Rat.num_div_den a.toRat, ← Rat.num_div_den b.toRat]
  rw [div_add_div _ _ (by exact_mod_cast a.toRat.den_nz) (by exact_mod_cast b.toRat.den_nz)]
  ring

theorem lit_rat_mul_spec (a b : num.Rational) :
    lit.rat_mul a b = ok (num.Rational.ofRat (a.toRat * b.toRat)) := by
  unfold lit.rat_mul
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.mul_spec,
    num.Integer.toInt_ofInt, Std.bind_ok]
  rw [lit_rat_spec _ _ (by simp [num.Integer.toInt_ofInt])]
  congr 2
  simp only [num.Integer.toInt_ofInt]
  push_cast
  conv => rhs; rw [← Rat.num_div_den a.toRat, ← Rat.num_div_den b.toRat]
  rw [div_mul_div_comm]

theorem lit_rat_neg_spec (a : num.Rational) :
    lit.rat_neg a = ok (num.Rational.ofRat (-a.toRat)) := by
  unfold lit.rat_neg
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.neg_spec,
    num.Integer.toInt_ofInt, Std.bind_ok]
  rw [lit_rat_spec _ _ (by simp [num.Integer.toInt_ofInt])]
  congr 2
  simp only [num.Integer.toInt_ofInt]
  push_cast
  conv => rhs; rw [← Rat.num_div_den a.toRat]
  rw [neg_div]

theorem lit_rat_from_integer_spec (n : num.Integer) :
    lit.rat_from_integer n = ok (num.Rational.ofRat (n.toInt : ℚ)) := by
  unfold lit.rat_from_integer
  simp only [num.Integer.one_spec, Std.bind_ok]
  rw [lit_rat_spec _ _ (by simp [num.Integer.toInt_ofInt])]
  simp [num.Integer.toInt_ofInt]

theorem lit_rat_sgn_spec (a : num.Rational) :
    ∃ r : Std.I32, lit.rat_sgn a = ok r ∧ r.val = Int.sign a.toRat.num := by
  unfold lit.rat_sgn
  simp only [num.Rational.numerator_spec, Std.bind_ok]
  obtain ⟨r, hr, hv⟩ := num.Integer.sgn_spec (num.Integer.ofInt a.toRat.num)
  exact ⟨r, hr, by rw [hv, num.Integer.toInt_ofInt]⟩

theorem lit_rat_floor_spec (a : num.Rational) :
    lit.rat_floor a = ok (num.Integer.ofInt (Rat.floor a.toRat)) := by
  unfold lit.rat_floor
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, Std.bind_ok]
  rw [num.Integer.euclidean_qr_spec _ _ (by simp [num.Integer.toInt_ofInt])]
  simp only [num.Integer.toInt_ofInt, Std.bind_ok]
  show ok (num.Integer.ofInt (Int.ediv a.toRat.num (a.toRat.den : Int))) = _
  congr 2
  unfold Rat.floor
  split
  · rename_i h; rw [h]; exact Int.ediv_one _
  · rfl

theorem lit_rat_div_spec (a b : num.Rational) (hb : b.toRat ≠ 0) :
    lit.rat_div a b = ok (num.Rational.ofRat (a.toRat / b.toRat)) := by
  unfold lit.rat_div
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.mul_spec,
    num.Integer.toInt_ofInt, Std.bind_ok]
  rw [lit_rat_spec _ _ (by simp [num.Integer.toInt_ofInt, Rat.num_ne_zero.mpr hb])]
  congr 2
  simp only [num.Integer.toInt_ofInt]
  push_cast
  conv => rhs; rw [← Rat.num_div_den a.toRat, ← Rat.num_div_den b.toRat]
  have h1 : ((a.toRat.den : Int) : ℚ) ≠ 0 := by exact_mod_cast a.toRat.den_nz
  have h2 : ((b.toRat.den : Int) : ℚ) ≠ 0 := by exact_mod_cast b.toRat.den_nz
  have h3 : ((b.toRat.num : Int) : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hb
  field_simp

theorem lit_rat_pow_spec (a : num.Rational) (k : Std.U32) :
    lit.rat_pow a k = ok (num.Rational.ofRat (a.toRat ^ k.val)) := by
  unfold lit.rat_pow
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.pow_spec,
    num.Integer.toInt_ofInt, Std.bind_ok]
  rw [lit_rat_spec _ _ (by simp [num.Integer.toInt_ofInt])]
  congr 2
  simp only [num.Integer.toInt_ofInt]
  push_cast
  conv => rhs; rw [← Rat.num_div_den a.toRat]
  rw [div_pow]

theorem sign_num_of_neg {q : ℚ} (h : q < 0) : Int.sign q.num = -1 :=
  Int.sign_eq_neg_one_of_neg (Rat.num_neg.mpr h)

theorem sign_num_of_eq {q : ℚ} (h : q = 0) : Int.sign q.num = 0 := by
  subst h; rfl

theorem sign_num_of_pos {q : ℚ} (h : 0 < q) : Int.sign q.num = 1 :=
  Int.sign_eq_one_of_pos (Rat.num_pos.mpr h)

/-- `rat_cmp`: by the signs where they differ or are both zero, else by
cross-multiplying; either way the order of the rationals. -/
theorem lit_rat_cmp_spec (a b : num.Rational) :
    lit.rat_cmp a b = ok (compare a.toRat b.toRat) := by
  unfold lit.rat_cmp
  obtain ⟨sa, hsa, hva⟩ := lit_rat_sgn_spec a
  obtain ⟨sb, hsb, hvb⟩ := lit_rat_sgn_spec b
  simp only [hsa, hsb, Std.bind_ok]
  rcases lt_trichotomy a.toRat 0 with ha | ha | ha <;>
  rcases lt_trichotomy b.toRat 0 with hb | hb | hb <;>
  (first
    | rw [sign_num_of_neg ha] at hva
    | rw [sign_num_of_eq ha] at hva
    | rw [sign_num_of_pos ha] at hva) <;>
  (first
    | rw [sign_num_of_neg hb] at hvb
    | rw [sign_num_of_eq hb] at hvb
    | rw [sign_num_of_pos hb] at hvb) <;>
  split_ifs <;>
  first
    | (exfalso; scalar_tac)
    | rw [compare_lt_iff_lt.mpr (by linarith)]
    | rw [compare_gt_iff_gt.mpr (by linarith)]
    | rw [compare_eq_iff_eq.mpr (by linarith)]
    | (simp only [num.Rational.numerator_spec, num.Rational.denominator_spec,
         num.Integer.mul_spec, num.Integer.partial_cmp_spec, num.Integer.toInt_ofInt,
         Std.bind_ok, core.option.Option.unwrap_or]
       congr 1
       rcases lt_trichotomy a.toRat b.toRat with h | h | h
       · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((Rat.lt_iff ..).mp h)]
       · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
       · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr ((Rat.lt_iff ..).mp h)])

/-! ## `eo::add` -/

/-- What `Lit::evaluate` gives for `eo::add` on two literals that stand
for terms. -/
noncomputable def addLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral i1, lit.Lit.Numeral i2 =>
    some (lit.Lit.Numeral (num.Integer.ofInt (i1.toInt + i2.toInt)))
  | lit.Lit.Rational q1, lit.Lit.Rational q2 =>
    some (lit.Lit.Rational (num.Rational.ofRat (q1.toRat + q2.toRat)))
  | lit.Lit.Binary c1, lit.Lit.Binary c2 =>
    if c1.size = c2.size then
      some (lit.Lit.Binary ⟨c1.size, num.Integer.ofInt
        (Int.emod (c1.value.toInt + c2.value.toInt) (2 ^ c1.size.val))⟩)
    else none
  | _, _ => none

theorem fold_int_add (args : Slice lit.Lit) (i1 i2 : num.Integer)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Numeral i2)) :
    lit.Lit.fold_int kind.EvalOp.Add i1 args ⦃ o =>
      o = addLit (lit.Lit.Numeral i1) (lit.Lit.Numeral i2) ⦄ := by
  unfold lit.Lit.fold_int lit.Lit.fold_int_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_int, num.Integer.clone_spec, num.Integer.add_spec]
  step as ⟨j, hj⟩
  unfold lit.Lit.fold_int_loop
  have hj2 : ¬ j < 2#usize := by scalar_tac
  simp [hlen, hj2, addLit]

theorem fold_rat_add (args : Slice lit.Lit) (q1 q2 : num.Rational)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Rational q2)) :
    lit.Lit.fold_rat kind.EvalOp.Add kind.LitKind.Rational q1 args ⦃ o =>
      o = addLit (lit.Lit.Rational q1) (lit.Lit.Rational q2) ⦄ := by
  unfold lit.Lit.fold_rat lit.Lit.fold_rat_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_rat, num.Rational.clone_spec, lit_rat_add_spec]
  step as ⟨j, hj⟩
  unfold lit.Lit.fold_rat_loop
  have hj2 : ¬ j < 2#usize := by scalar_tac
  simp [hlen, hj2, addLit, lit.Lit.rational, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
    kind.LitKind.read_discriminant]

theorem fold_bv_add (args : Slice lit.Lit) (c1 c2 : bitvec.BitVec)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Binary c2)) :
    lit.Lit.fold_bv kind.EvalOp.Add kind.LitKind.Binary c1 args ⦃ o =>
      o = addLit (lit.Lit.Binary c1) (lit.Lit.Binary c2) ⦄ := by
  unfold lit.Lit.fold_bv lit.Lit.all_of_size lit.Lit.all_of_size_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_bv, lit.Lit.is_bv_of_size,
    bitvec.BitVec.impl.size]
  by_cases hs : c2.size = c1.size
  · simp only [hs, ite_true, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp only [hlen, hj2, ite_false, Std.bind_ok, ite_true]
    unfold lit.Lit.fold_bv_loop1
    simp [hlen, h1 1#usize (by simp), lit.Lit.as_bv, bitvec.BitVec.Insts.CoreCloneClone.clone,
      core.clone.impls.CloneU32.clone, num.Integer.clone_spec, bitvec.BitVec.add,
      bitvec.BitVec.new, num.Integer.add_spec, num.Integer.mod_by_pow2_spec]
    step as ⟨k, hk⟩
    subst hk
    step as ⟨k2, hk2⟩
    have hk3 : ¬ (k2.val ≤ 1) := by scalar_tac
    simp [hk3, num.Integer.toInt_ofInt, lit.Lit.bitvec, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant, addLit, hs]
    unfold lit.Lit.fold_bv_loop1
    have hk4 : ¬ k2 < 2#usize := by scalar_tac
    simp [hlen, hk4]
  · simp only [hs, ite_false, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp [hlen, hj2, addLit, Ne.symm hs]

theorem lit_evaluate_add (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Add args ⦃ o => o = addLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have hl2 : Slice.length args = 2 := by simp [Slice.length, hargs]
  have h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok l2 := by
    intro i hi; simp [Slice.index_usize, hargs, hi]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
  first
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne]
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [addLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp only [lit.Lit.evaluate_nary, h0, Std.bind_ok, ite_true]
     first
     | (simp [lit.Lit.fold_str, addLit]; done)
     | (unfold lit.Lit.fold_bool lit.Lit.fold_bool_loop
        simp [hlen, h1 1#usize (by simp), lit.Lit.as_bool]
        step as ⟨j, hj⟩
        unfold lit.Lit.fold_bool_loop
        have hj2 : ¬ j < 2#usize := by scalar_tac
        simp [hlen, hj2, addLit])
     | exact fold_int_add args _ _ hlen h1
     | exact fold_rat_add args _ _ hlen h1
     | exact fold_bv_add args _ _ hlen h1)

theorem Store.rep_numeral_data {s : Store} {a : Term} {i : Int}
    (ha : s.Rep a (Eo.Term.Numeral i)) :
    s.nodes.val[a.val]! = TermData.Literal (lit.Lit.Numeral (num.Integer.ofInt i)) := by
  obtain ⟨hh, _⟩ := ha
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
  cases hh with
  | lit _ _ _ hd => exact hd

theorem Store.rep_rational_data {s : Store} {a : Term} {q : ℚ}
    (ha : s.Rep a (Eo.Term.Rational q)) :
    s.nodes.val[a.val]! = TermData.Literal (lit.Lit.Rational (num.Rational.ofRat q)) := by
  obtain ⟨hh, _⟩ := ha
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
  cases hh with
  | lit _ _ _ hd => exact hd

/-- `eo::add` of two binaries of the same width, as the runtime computes it. -/
theorem eo_add_binary (w n1 n2 : Int) (h1 : Tree.okBv w n1) (h2 : Tree.okBv w n2) :
    Eo.__eo_add (Eo.Term.Binary w n1) (Eo.Term.Binary w n2) =
      Eo.Term.Binary w ((n1 + n2) % 2 ^ w.toNat) ∧
    Tree.okBv w ((n1 + n2) % 2 ^ w.toNat) := by
  obtain ⟨hw0, hw1, hn1, hn1'⟩ := h1
  obtain ⟨-, -, hn2, hn2'⟩ := h2
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  refine ⟨?_, hw0, hw1, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
  simp [Eo.__eo_add, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not,
    SmtEval.native_mod_total, SmtEval.native_zplus, hp]

theorem Store.builtin_spec_add (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Add args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_add x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Add 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_add Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_add]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_add x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_add; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_add x y = Eo.Term.Stuck := by
        unfold Eo.__eo_add
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_rational_data ha⟩, ⟨_, Store.rep_rational_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_binary_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_add (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [addLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_add] using hinv.rep_stuck⟩)
        | (simp only [addLit, num.Integer.toInt_ofInt]
           have he : Eo.__eo_add (Eo.Term.Numeral i1) (Eo.Term.Numeral i2) =
               Eo.Term.Numeral (i1 + i2) := rfl
           rw [he]
           exact Store.literal_numeral_spec s _ hinv h64)
        | (simp only [addLit, num.Rational.toRat_ofRat]
           have he : Eo.__eo_add (Eo.Term.Rational q1) (Eo.Term.Rational q2) =
               Eo.Term.Rational (q1 + q2) := rfl
           rw [he]
           exact Store.literal_rational_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             obtain ⟨he, hok⟩ := eo_add_binary w1 n1 n2 hok1 hok2
             rw [he]
             have hl : addLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Binary (Tree.bvOf w1 ((n1 + n2) % 2 ^ w1.toNat))) := by
               have hs := Tree.u32Wrap_val w1.toNat (by obtain ⟨_, h, _⟩ := hok1; omega)
               simp [addLit, Tree.bvOf, num.Integer.toInt_ofInt, hs]
               rfl
             rw [hl]
             exact Store.literal_binary_spec s _ _ hok hinv h64
           · have hl : addLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [addLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_add (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_add, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)

/-! ## `eo::mul` -/

/-- What `Lit::evaluate` gives for `eo::mul` on two literals that stand
for terms. -/
noncomputable def mulLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral i1, lit.Lit.Numeral i2 =>
    some (lit.Lit.Numeral (num.Integer.ofInt (i1.toInt * i2.toInt)))
  | lit.Lit.Rational q1, lit.Lit.Rational q2 =>
    some (lit.Lit.Rational (num.Rational.ofRat (q1.toRat * q2.toRat)))
  | lit.Lit.Binary c1, lit.Lit.Binary c2 =>
    if c1.size = c2.size then
      some (lit.Lit.Binary ⟨c1.size, num.Integer.ofInt
        (Int.emod (c1.value.toInt * c2.value.toInt) (2 ^ c1.size.val))⟩)
    else none
  | _, _ => none

theorem fold_int_mul (args : Slice lit.Lit) (i1 i2 : num.Integer)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Numeral i2)) :
    lit.Lit.fold_int kind.EvalOp.Mul i1 args ⦃ o =>
      o = mulLit (lit.Lit.Numeral i1) (lit.Lit.Numeral i2) ⦄ := by
  unfold lit.Lit.fold_int lit.Lit.fold_int_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_int, num.Integer.clone_spec, num.Integer.mul_spec]
  step as ⟨j, hj⟩
  unfold lit.Lit.fold_int_loop
  have hj2 : ¬ j < 2#usize := by scalar_tac
  simp [hlen, hj2, mulLit]

theorem fold_rat_mul (args : Slice lit.Lit) (q1 q2 : num.Rational)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Rational q2)) :
    lit.Lit.fold_rat kind.EvalOp.Mul kind.LitKind.Rational q1 args ⦃ o =>
      o = mulLit (lit.Lit.Rational q1) (lit.Lit.Rational q2) ⦄ := by
  unfold lit.Lit.fold_rat lit.Lit.fold_rat_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_rat, num.Rational.clone_spec, lit_rat_mul_spec]
  step as ⟨j, hj⟩
  unfold lit.Lit.fold_rat_loop
  have hj2 : ¬ j < 2#usize := by scalar_tac
  simp [hlen, hj2, mulLit, lit.Lit.rational, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
    kind.LitKind.read_discriminant]

theorem fold_bv_mul (args : Slice lit.Lit) (c1 c2 : bitvec.BitVec)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Binary c2)) :
    lit.Lit.fold_bv kind.EvalOp.Mul kind.LitKind.Binary c1 args ⦃ o =>
      o = mulLit (lit.Lit.Binary c1) (lit.Lit.Binary c2) ⦄ := by
  unfold lit.Lit.fold_bv lit.Lit.all_of_size lit.Lit.all_of_size_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_bv, lit.Lit.is_bv_of_size,
    bitvec.BitVec.impl.size]
  by_cases hs : c2.size = c1.size
  · simp only [hs, ite_true, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp only [hlen, hj2, ite_false, Std.bind_ok, ite_true]
    unfold lit.Lit.fold_bv_loop1
    simp [hlen, h1 1#usize (by simp), lit.Lit.as_bv, bitvec.BitVec.Insts.CoreCloneClone.clone,
      core.clone.impls.CloneU32.clone, num.Integer.clone_spec, bitvec.BitVec.mul,
      bitvec.BitVec.new, num.Integer.mul_spec, num.Integer.mod_by_pow2_spec]
    step as ⟨k, hk⟩
    subst hk
    step as ⟨k2, hk2⟩
    have hk3 : ¬ (k2.val ≤ 1) := by scalar_tac
    simp [hk3, num.Integer.toInt_ofInt, lit.Lit.bitvec, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant, mulLit, hs]
    unfold lit.Lit.fold_bv_loop1
    have hk4 : ¬ k2 < 2#usize := by scalar_tac
    simp [hlen, hk4]
  · simp only [hs, ite_false, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp [hlen, hj2, mulLit, Ne.symm hs]

theorem lit_evaluate_mul (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Mul args ⦃ o => o = mulLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have hl2 : Slice.length args = 2 := by simp [Slice.length, hargs]
  have h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok l2 := by
    intro i hi; simp [Slice.index_usize, hargs, hi]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
  first
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne]
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [mulLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp only [lit.Lit.evaluate_nary, h0, Std.bind_ok, ite_true]
     first
     | (simp [lit.Lit.fold_str, mulLit]; done)
     | (unfold lit.Lit.fold_bool lit.Lit.fold_bool_loop
        simp [hlen, h1 1#usize (by simp), lit.Lit.as_bool]
        step as ⟨j, hj⟩
        unfold lit.Lit.fold_bool_loop
        have hj2 : ¬ j < 2#usize := by scalar_tac
        simp [hlen, hj2, mulLit])
     | exact fold_int_mul args _ _ hlen h1
     | exact fold_rat_mul args _ _ hlen h1
     | exact fold_bv_mul args _ _ hlen h1)

/-- `eo::mul` of two binaries of the same width, as the runtime computes it. -/
theorem eo_mul_binary (w n1 n2 : Int) (h1 : Tree.okBv w n1) (h2 : Tree.okBv w n2) :
    Eo.__eo_mul (Eo.Term.Binary w n1) (Eo.Term.Binary w n2) =
      Eo.Term.Binary w ((n1 * n2) % 2 ^ w.toNat) ∧
    Tree.okBv w ((n1 * n2) % 2 ^ w.toNat) := by
  obtain ⟨hw0, hw1, hn1, hn1'⟩ := h1
  obtain ⟨-, -, hn2, hn2'⟩ := h2
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  refine ⟨?_, hw0, hw1, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
  simp [Eo.__eo_mul, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not,
    SmtEval.native_mod_total, SmtEval.native_zmult, hp]

theorem Store.builtin_spec_mul (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Mul args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_mul x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Mul 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_mul Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_mul]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_mul x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_mul; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_mul x y = Eo.Term.Stuck := by
        unfold Eo.__eo_mul
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_rational_data ha⟩, ⟨_, Store.rep_rational_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_binary_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_mul (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [mulLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_mul] using hinv.rep_stuck⟩)
        | (simp only [mulLit, num.Integer.toInt_ofInt]
           have he : Eo.__eo_mul (Eo.Term.Numeral i1) (Eo.Term.Numeral i2) =
               Eo.Term.Numeral (i1 * i2) := rfl
           rw [he]
           exact Store.literal_numeral_spec s _ hinv h64)
        | (simp only [mulLit, num.Rational.toRat_ofRat]
           have he : Eo.__eo_mul (Eo.Term.Rational q1) (Eo.Term.Rational q2) =
               Eo.Term.Rational (q1 * q2) := rfl
           rw [he]
           exact Store.literal_rational_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             obtain ⟨he, hok⟩ := eo_mul_binary w1 n1 n2 hok1 hok2
             rw [he]
             have hl : mulLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Binary (Tree.bvOf w1 ((n1 * n2) % 2 ^ w1.toNat))) := by
               have hs := Tree.u32Wrap_val w1.toNat (by obtain ⟨_, h, _⟩ := hok1; omega)
               simp [mulLit, Tree.bvOf, num.Integer.toInt_ofInt, hs]
               rfl
             rw [hl]
             exact Store.literal_binary_spec s _ _ hok hinv h64
           · have hl : mulLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [mulLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_mul (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_mul, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)

/-! ## `eo::to_q` -/

/-- `Lit::evaluate` of `eo::to_q` on one literal. -/
theorem lit_evaluate_to_q (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.ToRat args ⦃ o => o = (match l with
      | lit.Lit.Numeral i => some (lit.Lit.Rational (num.Rational.ofRat (i.toInt : ℚ)))
      | lit.Lit.Rational q => some (lit.Lit.Rational q)
      | lit.Lit.Decimal q => some (lit.Lit.Rational q)
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l <;>
  · simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [lit_rat_from_integer_spec, lit_clone_eq, num.Rational.clone_spec]

theorem Store.builtin_spec_to_q (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.ToRat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_to_q x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.ToRat 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_one hargs ha as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_q Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_to_q]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_q x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_to_q
        split <;> first
          | rfl
          | (exfalso
             simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
             cases hh with | lit _ _ _ hd => exact ho _ hd)
          | simp_all
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l, hv, hd⟩ := ho
      simp only
      step with lit_evaluate_to_q (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
      subst ho1
      obtain ⟨hh, he⟩ := ha
      generalize hxe : Embedded.enc x = tx at hh
      cases hh with
      | lit _ l' _ hd' =>
        have hl : l' = l := by
          have h := hd'.symm.trans hd
          injection h
        subst hl
        rcases Embed.inv_Term_lit (by simpa [Embed.embedded_enc_Term] using hxe) with
          ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_q] using hinv.rep_stuck⟩
        · simp only [num.Integer.toInt_ofInt]
          have hv : Eo.__eo_to_q (Eo.Term.Numeral i) = Eo.Term.Rational (i : ℚ) := by
            simp [Eo.__eo_to_q, SmtEval.native_to_real, SmtEval.native_mk_rational]
          rw [hv]
          exact Store.literal_rational_spec s _ hinv h64
        · have hv : Eo.__eo_to_q (Eo.Term.Rational q) = Eo.Term.Rational q := rfl
          rw [hv]
          exact Store.literal_rational_spec s _ hinv h64
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_q] using hinv.rep_stuck⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_q] using hinv.rep_stuck⟩
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

/-! ## `eo::is_neg` -/

/-- `Lit::evaluate` of `eo::is_neg` on one literal. -/
theorem lit_evaluate_is_neg (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.IsNeg args ⦃ o => o = (match l with
      | lit.Lit.Numeral i => some (lit.Lit.Boolean (decide (i.toInt < 0)))
      | lit.Lit.Rational q => some (lit.Lit.Boolean (decide (q.toRat < 0)))
      | lit.Lit.Decimal q => some (lit.Lit.Boolean (decide (q.toRat < 0)))
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  have hsgn : ∀ (r : Std.I32) (z : Int), r.val = Int.sign z → (r = (-1)#i32 ↔ z < 0) := by
    intro r z hv
    rw [← Int.sign_eq_neg_one_iff_neg, ← hv]
    constructor
    · rintro rfl; rfl
    · intro h; apply IScalar.eq_of_val_eq; simp [h]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l
  case Numeral i =>
    obtain ⟨r, hr, hv⟩ := num.Integer.sgn_spec i
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [hr, hsgn r _ hv]
  case Rational q =>
    obtain ⟨r, hr, hv⟩ := lit_rat_sgn_spec q
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [hr, hsgn r _ hv, Rat.num_neg]
  case Decimal q =>
    obtain ⟨r, hr, hv⟩ := lit_rat_sgn_spec q
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [hr, hsgn r _ hv, Rat.num_neg]
  all_goals
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp

theorem Store.builtin_spec_is_neg (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsNeg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_neg x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsNeg 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_one hargs ha as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_is_neg Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_is_neg]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_is_neg x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_is_neg
        split <;> first
          | rfl
          | (exfalso
             simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
             cases hh with | lit _ _ _ hd => exact ho _ hd)
          | simp_all
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l, hv, hd⟩ := ho
      simp only
      step with lit_evaluate_is_neg (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
      subst ho1
      obtain ⟨hh, he⟩ := ha
      generalize hxe : Embedded.enc x = tx at hh
      cases hh with
      | lit _ l' _ hd' =>
        have hl : l' = l := by
          have h := hd'.symm.trans hd
          injection h
        subst hl
        rcases Embed.inv_Term_lit (by simpa [Embed.embedded_enc_Term] using hxe) with
          ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_is_neg] using hinv.rep_stuck⟩
        · simp only [num.Integer.toInt_ofInt]
          have hv : Eo.__eo_is_neg (Eo.Term.Numeral i) = Eo.Term.Boolean (decide (i < 0)) := by
            simp [Eo.__eo_is_neg, SmtEval.native_zlt]
          rw [hv]
          exact Store.literal_boolean_spec s _ hinv h64
        · simp only [num.Rational.toRat_ofRat]
          have hv : Eo.__eo_is_neg (Eo.Term.Rational q) = Eo.Term.Boolean (decide (q < 0)) := by
            simp [Eo.__eo_is_neg, SmtEval.native_qlt, SmtEval.native_mk_rational]
          rw [hv]
          exact Store.literal_boolean_spec s _ hinv h64
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_is_neg] using hinv.rep_stuck⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_is_neg] using hinv.rep_stuck⟩
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

/-! ## `eo::to_z` -/

/-- What `eo::to_z` gives of a string: of one character its code point, or
-1 for one that is no character (above 196607, MAX_CODE_POINT), as logos's
`native_str_to_code` (the runtime's check, option (c)). -/
noncomputable def toZStr (e : eostring.EoString) : Option lit.Lit :=
  if e.val.length = 1 then
    some (lit.Lit.Numeral (num.Integer.ofInt
      (if (e.val[0]!).val ≤ 196607 then ((e.val[0]!).val : Int) else -1)))
  else none

/-- `Lit::evaluate` of `eo::to_z` on one literal. -/
theorem lit_evaluate_to_z (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.ToInt args ⦃ o => o = (match l with
      | lit.Lit.Numeral i => some (lit.Lit.Numeral i)
      | lit.Lit.Rational q => some (lit.Lit.Numeral (num.Integer.ofInt (Rat.floor q.toRat)))
      | lit.Lit.Decimal q => some (lit.Lit.Numeral (num.Integer.ofInt (Rat.floor q.toRat)))
      | lit.Lit.Binary b => some (lit.Lit.Numeral b.value)
      | lit.Lit.Str e => toZStr e
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l
  case Str e =>
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp only [lit.Lit.evaluate_to_int, Std.bind_ok, eostring.EoString.len, alloc.vec.Vec.len,
      toZStr]
    by_cases h1 : e.val.length = 1
    · have hl : (alloc.vec.Vec.len e) = 1#usize := by
        apply UScalar.eq_of_val_eq; simpa [alloc.vec.Vec.len] using h1
      simp [h1, eostring.EoString.code_points, Slice.index_usize, max_code_point_eq,
        num.Integer.from_u32_spec, num.Integer.one_spec, num.Integer.neg_spec,
        num.Integer.toInt_ofInt, alloc.vec.Vec.deref]
      have h0' : (e.val[0]! : Std.U32) = e.val[0] := by
        simp [List.getElem!_eq_getElem?_getD, h1]
      have hu : ∀ h, Usize.ofNatCore 1 h = 1#usize := fun _ => rfl
      by_cases hc : (e.val[0]).val ≤ 196607 <;> simp [hc, h0', hu]
    · have hl : ¬ (alloc.vec.Vec.len e) = 1#usize := by
        intro h; apply h1; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len] using this
      simp [h1, hl]
  all_goals
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [lit.Lit.evaluate_to_int, lit_rat_floor_spec, lit_clone_eq, num.Integer.clone_spec,
      bitvec.BitVec.impl.value]

theorem Store.builtin_spec_to_z (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.ToInt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_to_z x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.ToInt 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_one hargs ha as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_z Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_to_z]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_z x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_to_z
        split <;> first
          | rfl
          | (exfalso
             simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
             cases hh with | lit _ _ _ hd => exact ho _ hd)
          | simp_all
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l, hv, hd⟩ := ho
      simp only
      step with lit_evaluate_to_z (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
      subst ho1
      obtain ⟨hh, he⟩ := ha
      generalize hxe : Embedded.enc x = tx at hh
      cases hh with
      | lit _ l' _ hd' =>
        have hl : l' = l := by
          have h := hd'.symm.trans hd
          injection h
        subst hl
        rcases Embed.inv_Term_lit (by simpa [Embed.embedded_enc_Term] using hxe) with
          ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_z] using hinv.rep_stuck⟩
        · have hv : Eo.__eo_to_z (Eo.Term.Numeral i) = Eo.Term.Numeral i := rfl
          rw [hv]
          exact Store.literal_numeral_spec s _ hinv h64
        · simp only [num.Rational.toRat_ofRat]
          have hv : Eo.__eo_to_z (Eo.Term.Rational q) = Eo.Term.Numeral (Rat.floor q) := by
            simp [Eo.__eo_to_z, SmtEval.native_to_int]
          rw [hv]
          exact Store.literal_numeral_spec s _ hinv h64
        · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
          have hval := Tree.strOf_val str he
          rcases str with _ | ⟨c, _ | ⟨c2, rest⟩⟩
          · simp only [toZStr, hval, List.map_nil, List.length_nil, zero_ne_one, ite_false,
              Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv, Store.Grows.refl s, by
              simpa [Eo.__eo_to_z, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_str_len]
                using hinv.rep_stuck⟩
          · have hc : c < 2 ^ 32 := he.2 c (by simp)
            have hw := Tree.u32Wrap_val c hc
            simp only [toZStr, hval, List.map_cons, List.map_nil, List.length_singleton, ite_true,
              List.getElem!_cons_zero, hw]
            have hv : Eo.__eo_to_z (Eo.Term.String [c]) =
                Eo.Term.Numeral (if c ≤ 196607 then (c : Int) else -1) := by
              simp [Eo.__eo_to_z, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_str_len,
                SmtEval.native_str_to_code, SmtEval.native_char_valid,
                SmtEval.native_z_max_code_point]
            rw [hv]
            exact Store.literal_numeral_spec s _ hinv h64
          · simp only [toZStr, hval, List.map_cons, List.length_cons, List.length_map]
            have h2 : ¬ (rest.length + 1 + 1 = 1) := by omega
            simp only [h2, ite_false, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            have h3 : ¬ ((rest.length : Int) + 1 = 0) := by omega
            exact ⟨hinv, Store.Grows.refl s, by
              simpa [Eo.__eo_to_z, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_str_len, h3]
                using hinv.rep_stuck⟩
        · have hv : Eo.__eo_to_z (Eo.Term.Binary w n) = Eo.Term.Numeral n := rfl
          rw [hv]
          exact Store.literal_numeral_spec s _ hinv h64
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

/-! ## `eo::not` -/

/-- `Lit::evaluate` of `eo::not` on one literal. -/
theorem lit_evaluate_not (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.Not args ⦃ o => o = (match l with
      | lit.Lit.Boolean b => some (lit.Lit.Boolean (!b))
      | lit.Lit.Binary c => some (lit.Lit.Binary ⟨c.size, num.Integer.ofInt
          (Int.emod (2 ^ c.size.val + -(c.value.toInt + 1)) (2 ^ c.size.val))⟩)
      | lit.Lit.Hex c => some (lit.Lit.Hex ⟨c.size, num.Integer.ofInt
          (Int.emod (2 ^ c.size.val + -(c.value.toInt + 1)) (2 ^ c.size.val))⟩)
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l <;>
  · simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [lit.Lit.evaluate_not, bitvec.BitVec.not, bitvec.pow2, num.Integer.from_u32_spec, num.Integer.pow_spec, num.Integer.one_spec, num.Integer.add_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec, lit.Lit.bitvec, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq, kind.LitKind.read_discriminant]

theorem Store.builtin_spec_not (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Not args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_not x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Not 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_one hargs ha as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_not Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_not]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_not x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_not
        split <;> first
          | rfl
          | (exfalso
             simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
             cases hh with | lit _ _ _ hd => exact ho _ hd)
          | simp_all
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l, hv, hd⟩ := ho
      simp only
      step with lit_evaluate_not (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
      subst ho1
      obtain ⟨hh, he⟩ := ha
      generalize hxe : Embedded.enc x = tx at hh
      cases hh with
      | lit _ l' _ hd' =>
        have hl : l' = l := by
          have h := hd'.symm.trans hd
          injection h
        subst hl
        rcases Embed.inv_Term_lit (by simpa [Embed.embedded_enc_Term] using hxe) with
          ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
        · have hv : Eo.__eo_not (Eo.Term.Boolean b) = Eo.Term.Boolean (!b) := by
            simp [Eo.__eo_not, SmtEval.native_not]
          rw [hv]
          exact Store.literal_boolean_spec s _ hinv h64
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_not] using hinv.rep_stuck⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_not] using hinv.rep_stuck⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_not] using hinv.rep_stuck⟩
        · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
          obtain ⟨hw0, hw1, hn0, hn1⟩ := he
          have hs := Tree.u32Wrap_val w.toNat (by omega)
          have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
          have hok : Tree.okBv w ((2 ^ w.toNat + -(n + 1)) % 2 ^ w.toNat) :=
            ⟨hw0, hw1, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
          have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
            simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, not_lt.mpr hw0]
          have hv : Eo.__eo_not (Eo.Term.Binary w n) =
              Eo.Term.Binary w ((2 ^ w.toNat + -(n + 1)) % 2 ^ w.toNat) := by
            simp [Eo.__eo_not, SmtEval.native_mod_total, SmtEval.native_binary_not,
              SmtEval.native_zplus, SmtEval.native_zneg, hp]
          rw [hv]
          have hl : (⟨(Tree.bvOf w n).size, num.Integer.ofInt
              (Int.emod (2 ^ (Tree.bvOf w n).size.val + -((Tree.bvOf w n).value.toInt + 1))
                (2 ^ (Tree.bvOf w n).size.val))⟩ : bitvec.BitVec) =
              Tree.bvOf w ((2 ^ w.toNat + -(n + 1)) % 2 ^ w.toNat) := by
            have he : ∀ a b : Int, Int.emod a b = a % b := fun _ _ => rfl
            simp [Tree.bvOf, num.Integer.toInt_ofInt, hs, he]
          simp only [hl]
          exact Store.literal_binary_spec s _ _ hok hinv h64
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

/-! ## `eo::neg` -/

theorem bv_neg_emod (v : Int) (k : Nat) :
    ((2 ^ k + -(v + 1)) % 2 ^ k + 1 % 2 ^ k) % 2 ^ k = (-v) % 2 ^ k := by
  rw [← Int.add_emod]
  have : 2 ^ k + -(v + 1) + 1 = -v + 2 ^ k * 1 := by ring
  rw [this, Int.add_mul_emod_self_left]

/-- `Lit::evaluate` of `eo::neg` on one literal. -/
theorem lit_evaluate_neg (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.Neg args ⦃ o => o = (match l with
      | lit.Lit.Numeral i => some (lit.Lit.Numeral (num.Integer.ofInt (-i.toInt)))
      | lit.Lit.Rational q => some (lit.Lit.Rational (num.Rational.ofRat (-q.toRat)))
      | lit.Lit.Decimal q => some (lit.Lit.Decimal (num.Rational.ofRat (-q.toRat)))
      | lit.Lit.Binary c => some (lit.Lit.Binary ⟨c.size, num.Integer.ofInt
          (Int.emod (-c.value.toInt) (2 ^ c.size.val))⟩)
      | lit.Lit.Hex c => some (lit.Lit.Hex ⟨c.size, num.Integer.ofInt
          (Int.emod (-c.value.toInt) (2 ^ c.size.val))⟩)
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  have he : ∀ a b : Int, Int.emod a b = a % b := fun _ _ => rfl
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l <;>
  · simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [lit.Lit.evaluate_neg, bitvec.BitVec.neg, bitvec.BitVec.not, bitvec.BitVec.add, bitvec.pow2, num.Integer.from_u32_spec, num.Integer.pow_spec, num.Integer.one_spec, num.Integer.add_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec, lit.Lit.bitvec, lit.Lit.rational, lit_rat_neg_spec, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq, kind.LitKind.read_discriminant, he, bv_neg_emod]

theorem Store.builtin_spec_neg (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Neg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_neg x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Neg 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_one hargs ha as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_neg Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_neg]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_neg x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_neg
        split <;> first
          | rfl
          | (exfalso
             simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
             cases hh with | lit _ _ _ hd => exact ho _ hd)
          | simp_all
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l, hv, hd⟩ := ho
      simp only
      step with lit_evaluate_neg (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
      subst ho1
      obtain ⟨hh, he⟩ := ha
      generalize hxe : Embedded.enc x = tx at hh
      cases hh with
      | lit _ l' _ hd' =>
        have hl : l' = l := by
          have h := hd'.symm.trans hd
          injection h
        subst hl
        rcases Embed.inv_Term_lit (by simpa [Embed.embedded_enc_Term] using hxe) with
          ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_neg] using hinv.rep_stuck⟩
        · simp only [num.Integer.toInt_ofInt]
          have hv : Eo.__eo_neg (Eo.Term.Numeral i) = Eo.Term.Numeral (-i) := rfl
          rw [hv]
          exact Store.literal_numeral_spec s _ hinv h64
        · simp only [num.Rational.toRat_ofRat]
          have hv : Eo.__eo_neg (Eo.Term.Rational q) = Eo.Term.Rational (-q) := rfl
          rw [hv]
          exact Store.literal_rational_spec s _ hinv h64
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_neg] using hinv.rep_stuck⟩
        · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
          obtain ⟨hw0, hw1, hn0, hn1⟩ := he
          have hs := Tree.u32Wrap_val w.toNat (by omega)
          have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
          have hok : Tree.okBv w ((-n) % 2 ^ w.toNat) :=
            ⟨hw0, hw1, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
          have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
            simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, not_lt.mpr hw0]
          have hv : Eo.__eo_neg (Eo.Term.Binary w n) =
              Eo.Term.Binary w ((-n) % 2 ^ w.toNat) := by
            simp [Eo.__eo_neg, SmtEval.native_mod_total, SmtEval.native_zneg, hp]
          rw [hv]
          have hl : (⟨(Tree.bvOf w n).size, num.Integer.ofInt
              (Int.emod (-(Tree.bvOf w n).value.toInt) (2 ^ (Tree.bvOf w n).size.val))⟩
                : bitvec.BitVec) =
              Tree.bvOf w ((-n) % 2 ^ w.toNat) := by
            have he : ∀ a b : Int, Int.emod a b = a % b := fun _ _ => rfl
            simp [Tree.bvOf, num.Integer.toInt_ofInt, hs, he]
          simp only [hl]
          exact Store.literal_binary_spec s _ _ hok hinv h64
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

/-! ## `eo::gt` -/

/-- What `Lit::evaluate` gives for `eo::gt` on two literals that stand
for terms. -/
noncomputable def gtLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral i1, lit.Lit.Numeral i2 =>
    some (lit.Lit.Boolean (decide (i2.toInt < i1.toInt)))
  | lit.Lit.Rational q1, lit.Lit.Rational q2 =>
    some (lit.Lit.Boolean (decide (q2.toRat < q1.toRat)))
  | lit.Lit.Binary c1, lit.Lit.Binary c2 =>
    if c1.size = c2.size then
      some (lit.Lit.Boolean (decide (c2.value.toInt < c1.value.toInt)))
    else none
  | _, _ => none

theorem lit_evaluate_gt (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Gt args ⦃ o => o = gtLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have hl2 : Slice.length args = 2 := by simp [Slice.length, hargs]
  have h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok l2 := by
    intro i hi; simp [Slice.index_usize, hargs, hi]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
  first
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne]
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [gtLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [lit.Lit.evaluate_gt, lit.Lit.arg, hlen, h1 1#usize (by simp), lit.Lit.as_rat,
       lit.Lit.as_bv, lit_rat_cmp_spec, core.cmp.PartialOrd.gt.trait_default,
       core.cmp.PartialOrd.gt.default, core.cmp.PartialOrd.gt_body, num.Integer.partial_cmp_spec,
       bitvec.BitVec.impl.size, bitvec.BitVec.impl.value, gtLit, compare_gt_iff_gt]
     all_goals first
       | (split <;> simp_all [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt, not_lt,
           le_of_lt]
          done)
       | skip)

theorem Store.builtin_spec_gt (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Gt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_gt x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Gt 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_gt Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_gt]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_gt x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_gt; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_gt x y = Eo.Term.Stuck := by
        unfold Eo.__eo_gt
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_rational_data ha⟩, ⟨_, Store.rep_rational_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_binary_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_gt (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [gtLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_gt] using hinv.rep_stuck⟩)
        | (simp only [gtLit, num.Integer.toInt_ofInt]
           have he : Eo.__eo_gt (Eo.Term.Numeral i1) (Eo.Term.Numeral i2) =
               Eo.Term.Boolean (decide (i2 < i1)) := by
             simp [Eo.__eo_gt, SmtEval.native_zlt]
           rw [he]
           exact Store.literal_boolean_spec s _ hinv h64)
        | (simp only [gtLit, num.Rational.toRat_ofRat]
           have he : Eo.__eo_gt (Eo.Term.Rational q1) (Eo.Term.Rational q2) =
               Eo.Term.Boolean (decide (q2 < q1)) := by
             simp [Eo.__eo_gt, SmtEval.native_qlt]
           rw [he]
           exact Store.literal_boolean_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             have he : Eo.__eo_gt (Eo.Term.Binary w1 n1) (Eo.Term.Binary w1 n2) =
                 Eo.Term.Boolean (decide (n2 < n1)) := by
               simp [Eo.__eo_gt, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq,
                 SmtEval.native_not, SmtEval.native_zlt]
             rw [he]
             have hl : gtLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Boolean (decide (n2 < n1))) := by
               simp [gtLit, Tree.bvOf, num.Integer.toInt_ofInt]
             rw [hl]
             exact Store.literal_boolean_spec s _ hinv h64
           · have hl : gtLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [gtLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_gt (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_gt, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)


/-! ## `eo::to_bin` -/

/-- What `Lit::evaluate` gives for `eo::to_bin` on two literals that stand
for terms: a width that fits in 32 bits, and a numeral or a binary, whose
value is reduced modulo `2 ^ width`. -/
noncomputable def toBinLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral w, lit.Lit.Numeral i =>
    if 0 ≤ w.toInt ∧ w.toInt < 2 ^ 32 then
      some (lit.Lit.Binary (Tree.bvOf w.toInt (Int.emod i.toInt (2 ^ w.toInt.toNat))))
    else none
  | lit.Lit.Numeral w, lit.Lit.Binary c =>
    if 0 ≤ w.toInt ∧ w.toInt < 2 ^ 32 then
      some (lit.Lit.Binary (Tree.bvOf w.toInt (Int.emod c.value.toInt (2 ^ w.toInt.toNat))))
    else none
  | _, _ => none

theorem lit_evaluate_to_bin (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.ToBin args ⦃ o => o = toBinLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok l2 := by simp [Slice.index_usize, hargs]
  have hne : core.slice.Slice.is_empty args = ok false := by
    simp [core.slice.Slice.is_empty, Slice.len, hargs]
  unfold lit.Lit.evaluate
  simp only [hne, h0, Std.bind_ok, Bool.false_eq_true, ite_false, ite_true]
  unfold lit.Lit.evaluate_to_bin
  cases l1 <;> simp only [TermLit] at ht1 <;> simp [lit.Lit.kind, lit.Lit.as_int, toBinLit]
  rename_i w
  simp only [num.Integer.fits_u32_spec]
  have h32 : (2 : Int) ^ 32 = 4294967296 := by norm_num
  by_cases hw : 0 ≤ w.toInt ∧ w.toInt < 2 ^ 32
  · obtain ⟨r, hr, hrv⟩ := num.Integer.to_u32_spec w
    rw [if_pos hw] at hrv
    have hrw : r = Tree.u32Wrap w.toInt.toNat := by
      apply UScalar.eq_of_val_eq
      rw [Tree.u32Wrap_val _ (by omega)]; omega
    have hpow : (2 : Int) ^ r.val = 2 ^ w.toInt.toNat := by
      congr 1; omega
    have hpow' : (2 : Int) ^ (Tree.u32Wrap w.toInt.toNat).val = 2 ^ w.toInt.toNat := by
      rw [Tree.u32Wrap_val _ (by omega)]
    have hlt : w.toInt < 4294967296 := by omega
    simp only [hw, decide_true, ite_true, hr, Std.bind_ok, lit.Lit.arg, hlen, h1]
    cases l2 <;> simp only [TermLit] at ht2 <;>
      simp [toBinLit, hw, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec,
        bitvec.BitVec.impl.value, Tree.bvOf, hrw, hpow', hlt]
  · rw [h32] at hw
    cases l2 <;> simp [hw, toBinLit]


/-- logos's `eo::to_bin` of a width in range and a numeral: the binary of
that width with the value reduced, which is in range. -/
theorem eo_to_bin_ok {w : Int} (hw : 0 ≤ w ∧ w < 2 ^ 32) (n : Int) :
    Eo.__eo_to_bin (Eo.Term.Numeral w) (Eo.Term.Numeral n) =
      Eo.Term.Binary w (Int.emod n (2 ^ w.toNat)) ∧ Tree.okBv w (Int.emod n (2 ^ w.toNat)) := by
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  refine ⟨?_, hw.1, hw.2, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
  simp [Eo.__eo_to_bin, Eo.__eo_mk_binary, SmtEval.native_ite, SmtEval.native_and,
    SmtEval.native_zleq, SmtEval.native_zlt, SmtEval.native_mod_total, hp, hw.1,
    show w < 4294967296 by omega]
  rfl

/-- The same of a width in range and a binary. -/
theorem eo_to_bin_ok_bin {w : Int} (hw : 0 ≤ w ∧ w < 2 ^ 32) (w1 n : Int) :
    Eo.__eo_to_bin (Eo.Term.Numeral w) (Eo.Term.Binary w1 n) =
      Eo.Term.Binary w (Int.emod n (2 ^ w.toNat)) ∧ Tree.okBv w (Int.emod n (2 ^ w.toNat)) := by
  obtain ⟨-, hok⟩ := eo_to_bin_ok hw n
  refine ⟨?_, hok⟩
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
  simp [Eo.__eo_to_bin, Eo.__eo_mk_binary, SmtEval.native_ite, SmtEval.native_and,
    SmtEval.native_zleq, SmtEval.native_zlt, SmtEval.native_mod_total, hp, hw.1,
    show w < 4294967296 by omega]
  rfl

/-- logos's `eo::to_bin` of a width out of range is stuck. -/
theorem eo_to_bin_bad {w : Int} (hw : ¬ (0 ≤ w ∧ w < 2 ^ 32)) (n : Int) :
    Eo.__eo_to_bin (Eo.Term.Numeral w) (Eo.Term.Numeral n) = Eo.Term.Stuck := by
  have : ¬ (0 ≤ w ∧ w < 4294967296) := by norm_num at hw ⊢; omega
  have hc : SmtEval.native_and (SmtEval.native_zleq 0 w) (SmtEval.native_zlt w 4294967296) =
      false := by
    unfold SmtEval.native_and SmtEval.native_zleq SmtEval.native_zlt
    by_cases h0 : 0 ≤ w
    · have h1 : ¬ w < 4294967296 := fun h => this ⟨h0, h⟩
      simp [h1]
    · simp [h0]
  unfold Eo.__eo_to_bin
  dsimp only
  rw [hc]
  rfl

theorem eo_to_bin_bad_bin {w : Int} (hw : ¬ (0 ≤ w ∧ w < 2 ^ 32)) (w1 n : Int) :
    Eo.__eo_to_bin (Eo.Term.Numeral w) (Eo.Term.Binary w1 n) = Eo.Term.Stuck := by
  have : ¬ (0 ≤ w ∧ w < 4294967296) := by norm_num at hw ⊢; omega
  have hc : SmtEval.native_and (SmtEval.native_zleq 0 w) (SmtEval.native_zlt w 4294967296) =
      false := by
    unfold SmtEval.native_and SmtEval.native_zleq SmtEval.native_zlt
    by_cases h0 : 0 ≤ w
    · have h1 : ¬ w < 4294967296 := fun h => this ⟨h0, h⟩
      simp [h1]
    · simp [h0]
  unfold Eo.__eo_to_bin
  dsimp only
  rw [hc]
  rfl

/-- `eo::to_bin` on handles of a width and a numeral or binary: logos's
`__eo_to_bin`. -/
theorem Store.builtin_spec_to_bin (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.ToBin args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_to_bin x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.ToBin 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_bin Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_to_bin; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_bin x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_to_bin; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_bin x y = Eo.Term.Stuck := by
        unfold Eo.__eo_to_bin
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_to_bin (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [toBinLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_bin] using hinv.rep_stuck⟩)
        | (by_cases hw : 0 ≤ i1 ∧ i1 < 2 ^ 32
           · have hv2 : ∀ n : Int, Eo.__eo_to_bin (Eo.Term.Numeral i1) (Eo.Term.Numeral n) =
                 Eo.Term.Binary i1 (Int.emod n (2 ^ i1.toNat)) ∧
                 Tree.okBv i1 (Int.emod n (2 ^ i1.toNat)) := fun n => eo_to_bin_ok hw n
             first
             | (obtain ⟨he, hok⟩ := hv2 i2
                rw [he]
                simp only [toBinLit, num.Integer.toInt_ofInt, hw, and_self, ite_true]
                exact Store.literal_binary_spec s _ _ hok hinv h64)
             | (obtain ⟨he, hok⟩ := eo_to_bin_ok_bin hw w2 n2
                rw [he]
                simp only [toBinLit, num.Integer.toInt_ofInt, hw, and_self, ite_true, Tree.bvOf]
                exact Store.literal_binary_spec s _ _ hok hinv h64)
           · first
             | (simp only [toBinLit, num.Integer.toInt_ofInt, hw, ite_false, Store.stuck_eq,
                  Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
                refine ⟨hinv, Store.Grows.refl s, ?_⟩
                rw [eo_to_bin_bad hw]; exact hinv.rep_stuck)
             | (simp only [toBinLit, num.Integer.toInt_ofInt, hw, ite_false, Store.stuck_eq,
                  Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
                refine ⟨hinv, Store.Grows.refl s, ?_⟩
                rw [eo_to_bin_bad_bin hw]; exact hinv.rep_stuck))


/-! ## `eo::pow` -/

/-- `rat_pow` raises the numerator and the denominator. -/
theorem rat_pow_spec (a : num.Rational) (e : Std.U32) :
    lit.rat_pow a e = ok (num.Rational.ofRat (a.toRat ^ e.val)) := by
  unfold lit.rat_pow
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.pow_spec,
    num.Integer.toInt_ofInt, Std.bind_ok]
  have hd : ((a.toRat.den : Int) ^ e.val) ≠ 0 := pow_ne_zero _ (by exact_mod_cast a.toRat.den_nz)
  rw [lit_rat_spec _ _ (by rw [num.Integer.toInt_ofInt]; exact hd)]
  congr 1
  simp only [num.Integer.toInt_ofInt]
  push_cast
  rw [← div_pow, Rat.num_div_den]

/-- What `Lit::evaluate` gives for `eo::pow` on two literals that stand for
terms: a numeral or a rational to an exponent that fits in 32 bits. -/
noncomputable def powLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral i, lit.Lit.Numeral e =>
    if 0 ≤ e.toInt ∧ e.toInt < 2 ^ 32 then
      some (lit.Lit.Numeral (num.Integer.ofInt (i.toInt ^ e.toInt.toNat)))
    else none
  | lit.Lit.Rational q, lit.Lit.Numeral e =>
    if 0 ≤ e.toInt ∧ e.toInt < 2 ^ 32 then
      some (lit.Lit.Rational (num.Rational.ofRat (q.toRat ^ e.toInt.toNat)))
    else none
  | _, _ => none

theorem lit_evaluate_pow (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Pow args ⦃ o => o = powLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok l2 := by simp [Slice.index_usize, hargs]
  have hne : core.slice.Slice.is_empty args = ok false := by
    simp [core.slice.Slice.is_empty, Slice.len, hargs]
  have h32 : (2 : Int) ^ 32 = 4294967296 := by norm_num
  unfold lit.Lit.evaluate
  simp only [hne, h0, Std.bind_ok, Bool.false_eq_true, ite_false, ite_true]
  unfold lit.Lit.evaluate_pow lit.Lit.int_arg
  simp only [lit.Lit.arg, hlen, h1, Std.bind_ok]
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
    simp [lit.Lit.kind, lit.Lit.as_int, powLit]
  all_goals
    rename_i x e
    simp only [num.Integer.fits_u32_spec]
    by_cases hw : 0 ≤ e.toInt ∧ e.toInt < 2 ^ 32
    · obtain ⟨r, hr, hrv⟩ := num.Integer.to_u32_spec e
      rw [if_pos hw] at hrv
      have hpow : r.val = e.toInt.toNat := by omega
      rw [h32] at hw
      simp [hw, hr, num.Integer.pow_spec, rat_pow_spec, lit.Lit.rational, hpow,
        kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq, kind.LitKind.read_discriminant]
    · rw [h32] at hw
      simp [hw]


/-- logos's `eo::pow` of a numeral to an exponent in range. -/
theorem eo_pow_num {i e : Int} (he : 0 ≤ e ∧ e < 2 ^ 32) :
    Eo.__eo_pow (Eo.Term.Numeral i) (Eo.Term.Numeral e) = Eo.Term.Numeral (i ^ e.toNat) := by
  have hc : SmtEval.native_and (SmtEval.native_zleq 0 e) (SmtEval.native_zlt e 4294967296) =
      true := by
    rw [show (2 : Int) ^ 32 = 4294967296 by norm_num] at he
    simp only [SmtEval.native_and, SmtEval.native_zleq, SmtEval.native_zlt, Bool.and_eq_true,
      decide_eq_true_eq]
    omega
  unfold Eo.__eo_pow
  dsimp only
  rw [hc]
  simp [SmtEval.native_ite, SmtEval.native_zexp_total, show ¬ e < 0 by omega]

/-- logos's `eo::pow` of a rational to an exponent in range. -/
theorem eo_pow_rat {q : ℚ} {e : Int} (he : 0 ≤ e ∧ e < 2 ^ 32) :
    Eo.__eo_pow (Eo.Term.Rational q) (Eo.Term.Numeral e) = Eo.Term.Rational (q ^ e.toNat) := by
  have hc : SmtEval.native_and (SmtEval.native_zleq 0 e) (SmtEval.native_zlt e 4294967296) =
      true := by
    rw [show (2 : Int) ^ 32 = 4294967296 by norm_num] at he
    simp only [SmtEval.native_and, SmtEval.native_zleq, SmtEval.native_zlt, Bool.and_eq_true,
      decide_eq_true_eq]
    omega
  unfold Eo.__eo_pow
  dsimp only
  rw [hc]
  simp [SmtEval.native_ite, Eo.native_qexp_total, show ¬ e < 0 by omega]

/-- logos's `eo::pow` to an exponent out of range is stuck. -/
theorem eo_pow_bad {i e : Int} (he : ¬ (0 ≤ e ∧ e < 2 ^ 32)) :
    Eo.__eo_pow (Eo.Term.Numeral i) (Eo.Term.Numeral e) = Eo.Term.Stuck := by
  have : ¬ (0 ≤ e ∧ e < 4294967296) := by norm_num at he ⊢; omega
  have hc : SmtEval.native_and (SmtEval.native_zleq 0 e) (SmtEval.native_zlt e 4294967296) =
      false := by
    unfold SmtEval.native_and SmtEval.native_zleq SmtEval.native_zlt
    by_cases h0 : 0 ≤ e
    · have h1 : ¬ e < 4294967296 := fun h => this ⟨h0, h⟩
      simp [h1]
    · simp [h0]
  unfold Eo.__eo_pow
  dsimp only
  rw [hc]
  rfl

theorem eo_pow_bad_rat {q : ℚ} {e : Int} (he : ¬ (0 ≤ e ∧ e < 2 ^ 32)) :
    Eo.__eo_pow (Eo.Term.Rational q) (Eo.Term.Numeral e) = Eo.Term.Stuck := by
  have : ¬ (0 ≤ e ∧ e < 4294967296) := by norm_num at he ⊢; omega
  have hc : SmtEval.native_and (SmtEval.native_zleq 0 e) (SmtEval.native_zlt e 4294967296) =
      false := by
    unfold SmtEval.native_and SmtEval.native_zleq SmtEval.native_zlt
    by_cases h0 : 0 ≤ e
    · have h1 : ¬ e < 4294967296 := fun h => this ⟨h0, h⟩
      simp [h1]
    · simp [h0]
  unfold Eo.__eo_pow
  dsimp only
  rw [hc]
  rfl

/-- `eo::pow` on handles of a numeral or a rational and an exponent: logos's
`__eo_pow`. -/
theorem Store.builtin_spec_pow (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Pow args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_pow x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Pow 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_pow Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_pow; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_pow x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_pow; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_pow x y = Eo.Term.Stuck := by
        unfold Eo.__eo_pow
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_rational_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_pow (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [powLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_pow] using hinv.rep_stuck⟩)
        | (by_cases he : 0 ≤ i2 ∧ i2 < 2 ^ 32
           · first
             | (rw [eo_pow_num he]
                simp only [powLit, num.Integer.toInt_ofInt, he, and_self, ite_true]
                exact Store.literal_numeral_spec s _ hinv h64)
             | (rw [eo_pow_rat he]
                simp only [powLit, num.Integer.toInt_ofInt, num.Rational.toRat_ofRat, he, and_self,
                  ite_true]
                exact Store.literal_rational_spec s _ hinv h64)
           · simp only [powLit, num.Integer.toInt_ofInt, he, ite_false, Store.stuck_eq,
               Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             refine ⟨hinv, Store.Grows.refl s, ?_⟩
             first
             | (rw [eo_pow_bad he]; exact hinv.rep_stuck)
             | (rw [eo_pow_bad_rat he]; exact hinv.rep_stuck))


/-! ## `eo::div` and `eo::mod` -/

/-- `pow2` is the power of two. -/
theorem bitvec_pow2_spec (k : Std.U32) :
    bitvec.pow2 k = ok (num.Integer.ofInt (2 ^ k.val)) := by
  unfold bitvec.pow2
  simp [num.Integer.from_u32_spec, num.Integer.pow_spec, num.Integer.toInt_ofInt]

/-- The sign of an integer is zero exactly when it is. -/
theorem integer_sgn_zero (a : num.Integer) :
    ∃ r : Std.I32, num.Integer.sgn a = ok r ∧ (r = 0#i32 ↔ a.toInt = 0) := by
  obtain ⟨r, hr, hv⟩ := num.Integer.sgn_spec a
  refine ⟨r, hr, ?_⟩
  constructor
  · intro h; subst h; simp at hv; exact Int.sign_eq_zero_iff_zero.mp hv.symm
  · intro h; apply IScalar.eq_of_val_eq; rw [hv, h]; rfl

/-- Unsigned division, total: all ones by zero. -/
theorem udiv_total_spec (a b : bitvec.BitVec) :
    bitvec.BitVec.unsigned_div_total a b = ok ⟨a.size, num.Integer.ofInt
      (if b.value.toInt = 0 then (2 ^ a.size.val - 1) % 2 ^ a.size.val
       else Int.ediv a.value.toInt b.value.toInt % 2 ^ a.size.val)⟩ := by
  unfold bitvec.BitVec.unsigned_div_total
  obtain ⟨r, hr, hz⟩ := integer_sgn_zero b.value
  simp only [hr, Std.bind_ok]
  by_cases h0 : b.value.toInt = 0
  · simp [hz.mpr h0, h0, bitvec_pow2_spec, num.Integer.one_spec, num.Integer.neg_spec,
      num.Integer.add_spec, num.Integer.toInt_ofInt, bitvec.BitVec.new,
      num.Integer.mod_by_pow2_spec, Int.sub_eq_add_neg]
    congr 1
    exact Int.add_emod_left _ _
  · have hr0 : ¬ r = 0#i32 := fun h => h0 (hz.mp h)
    simp [hr0, h0, num.Integer.euclidean_qr_spec _ _ h0, bitvec.BitVec.new,
      num.Integer.mod_by_pow2_spec, num.Integer.toInt_ofInt]
    rfl

/-- Unsigned remainder, total: the dividend by zero. -/
theorem urem_total_spec (a b : bitvec.BitVec) :
    bitvec.BitVec.unsigned_rem_total a b = ok ⟨a.size, num.Integer.ofInt
      (if b.value.toInt = 0 then a.value.toInt % 2 ^ a.size.val
       else Int.emod a.value.toInt b.value.toInt % 2 ^ a.size.val)⟩ := by
  unfold bitvec.BitVec.unsigned_rem_total
  obtain ⟨r, hr, hz⟩ := integer_sgn_zero b.value
  simp only [hr, Std.bind_ok]
  by_cases h0 : b.value.toInt = 0
  · simp [hz.mpr h0, h0, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec]
    rfl
  · have hr0 : ¬ r = 0#i32 := fun h => h0 (hz.mp h)
    simp [hr0, h0, num.Integer.euclidean_qr_spec _ _ h0, bitvec.BitVec.new,
      num.Integer.mod_by_pow2_spec, num.Integer.toInt_ofInt]
    rfl


/-- What `Lit::evaluate` gives for `eo::div` (`isDiv`) or `eo::mod` on two
literals that stand for terms. -/
noncomputable def divLit (isDiv : Bool) : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral n, lit.Lit.Numeral m =>
    if m.toInt = 0 then none
    else some (lit.Lit.Numeral (num.Integer.ofInt
      (if isDiv then Int.ediv n.toInt m.toInt else Int.emod n.toInt m.toInt)))
  | lit.Lit.Binary a, lit.Lit.Binary b =>
    if a.size = b.size then
      some (lit.Lit.Binary ⟨a.size, num.Integer.ofInt
        (if isDiv then
          (if b.value.toInt = 0 then (2 ^ a.size.val - 1) % 2 ^ a.size.val
           else Int.ediv a.value.toInt b.value.toInt % 2 ^ a.size.val)
         else
          (if b.value.toInt = 0 then a.value.toInt % 2 ^ a.size.val
           else Int.emod a.value.toInt b.value.toInt % 2 ^ a.size.val))⟩)
    else none
  | _, _ => none

theorem lit_evaluate_int_div (isDiv : Bool)
    (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate (if isDiv then kind.EvalOp.IntDiv else kind.EvalOp.IntMod) args ⦃ o =>
      o = divLit isDiv l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have hl2 : Slice.length args = 2 := by simp [Slice.length, hargs]
  have h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok l2 := by
    intro i hi; simp [Slice.index_usize, hargs, hi]
  cases isDiv <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop <;>
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
  first
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne]
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [divLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [lit.Lit.evaluate_int_div, lit.Lit.arg, hlen, h1 1#usize (by simp), lit.Lit.as_bv,
       divLit, udiv_total_spec, urem_total_spec, lit.Lit.bitvec,
       kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq, kind.LitKind.read_discriminant,
       bitvec.BitVec.impl.size]
     all_goals
       rename_i x y
       first
       | (obtain ⟨r, hr, hz⟩ := integer_sgn_zero y
          by_cases h0 : y.toInt = 0
          · simp [hr, hz.mpr h0, h0]
          · have hr0 : ¬ r = 0#i32 := fun h => h0 (hz.mp h)
            simp [hr, hr0, h0, num.Integer.euclidean_qr_spec _ _ h0])
       | (by_cases hs : x.size = y.size
          · simp [hs]
          · have hs' : ¬ (x.size.val = y.size.val) := fun h => hs (UScalar.eq_of_val_eq h)
            simp [hs, hs']))


/-- logos's `eo::div` and `eo::mod` of numerals: stuck by zero, else
Euclidean. -/
theorem eo_zdiv_num (n m : Int) :
    Eo.__eo_zdiv (Eo.Term.Numeral n) (Eo.Term.Numeral m) =
      if m = 0 then Eo.Term.Stuck else Eo.Term.Numeral (Int.ediv n m) := by
  by_cases h : m = 0
  · subst h; simp [Eo.__eo_zdiv, SmtEval.native_ite, SmtEval.native_zeq]
  · simp [Eo.__eo_zdiv, SmtEval.native_ite, SmtEval.native_zeq, SmtEval.native_div_total, h,
      Ne.symm h]
    rfl

theorem eo_zmod_num (n m : Int) :
    Eo.__eo_zmod (Eo.Term.Numeral n) (Eo.Term.Numeral m) =
      if m = 0 then Eo.Term.Stuck else Eo.Term.Numeral (Int.emod n m) := by
  by_cases h : m = 0
  · subst h; simp [Eo.__eo_zmod, SmtEval.native_ite, SmtEval.native_zeq]
  · simp [Eo.__eo_zmod, SmtEval.native_ite, SmtEval.native_zeq, SmtEval.native_mod_total, h,
      Ne.symm h]
    rfl

/-- logos's `eo::div` of two binaries of one width, as the runtime reduces
it. -/
theorem eo_zdiv_bin {w n1 n2 : Int} (h1 : Tree.okBv w n1) :
    Eo.__eo_zdiv (Eo.Term.Binary w n1) (Eo.Term.Binary w n2) =
      Eo.Term.Binary w (if n2 = 0 then (2 ^ w.toNat - 1) % 2 ^ w.toNat
        else Int.ediv n1 n2 % 2 ^ w.toNat) := by
  obtain ⟨hw0, -, -, -⟩ := h1
  have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  by_cases h : n2 = 0
  · subst h
    have hm : (2 ^ w.toNat - 1 : Int) % 2 ^ w.toNat = 2 ^ w.toNat - 1 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hm' : (-1 : Int) % 2 ^ w.toNat = 2 ^ w.toNat + -1 := by
      rw [← Int.add_emod_left (2 ^ w.toNat) (-1), ← Int.sub_eq_add_neg]; exact hm
    simp [Eo.__eo_zdiv, Eo.__eo_requires, SmtEval.native_ite, SmtEval.native_zeq,
      SmtEval.native_binary_max, SmtEval.native_zplus, SmtEval.native_zneg, Eo.native_teq,
      SmtEval.native_not, hp, Int.sub_eq_add_neg]
    exact hm'.symm
  · simp [Eo.__eo_zdiv, Eo.__eo_requires, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_teq,
      SmtEval.native_not, SmtEval.native_mod_total, SmtEval.native_div_total, hp, h, Ne.symm h]
    rfl

theorem eo_zmod_bin {w n1 n2 : Int} (h1 : Tree.okBv w n1) :
    Eo.__eo_zmod (Eo.Term.Binary w n1) (Eo.Term.Binary w n2) =
      Eo.Term.Binary w (if n2 = 0 then n1 % 2 ^ w.toNat
        else Int.emod n1 n2 % 2 ^ w.toNat) := by
  obtain ⟨hw0, -, hn0, hn1⟩ := h1
  have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
  by_cases h : n2 = 0
  · subst h
    have hm : n1 % 2 ^ w.toNat = n1 := Int.emod_eq_of_lt hn0 hn1
    simp [Eo.__eo_zmod, Eo.__eo_requires, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_teq,
      SmtEval.native_not, hm]
  · simp [Eo.__eo_zmod, Eo.__eo_requires, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_teq,
      SmtEval.native_not, SmtEval.native_mod_total, hp, h, Ne.symm h]
    rfl


/-- `eo::div` on handles of two numerals or two binaries: logos's `__eo_zdiv`. -/
theorem Store.builtin_spec_int_div (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IntDiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_zdiv x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IntDiv 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_zdiv Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_zdiv; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_zdiv x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_zdiv; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_zdiv x y = Eo.Term.Stuck := by
        unfold Eo.__eo_zdiv
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_binary_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have hev := lit_evaluate_int_div true (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2
      simp only [ite_true] at hev
      step with hev as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [divLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_zdiv] using hinv.rep_stuck⟩)
        | (rw [eo_zdiv_num]
           by_cases h0 : i2 = 0
           · simp only [divLit, num.Integer.toInt_ofInt, h0, ite_true, Store.stuck_eq, Std.bind_ok,
               WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
           · simp only [divLit, num.Integer.toInt_ofInt, h0, ite_false, Bool.false_eq_true,
               ite_true]
             exact Store.literal_numeral_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             rw [eo_zdiv_bin hok1]
             obtain ⟨hw0, hw1, -, -⟩ := hok1
             have hsz := Tree.u32Wrap_val w1.toNat (by omega)
             have hpos : (0 : Int) < 2 ^ w1.toNat := by positivity
             generalize hV : (if n2 = 0 then _ else _ : Int) = V
             have hokV : Tree.okBv w1 V := by
               refine ⟨hw0, hw1, ?_, ?_⟩ <;> rw [← hV] <;> split_ifs <;>
                 first | exact Int.emod_nonneg _ hpos.ne' | exact Int.emod_lt_of_pos _ hpos
             have hl : divLit true (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Binary (Tree.bvOf w1 V)) := by
               rw [← hV]
               simp [divLit, Tree.bvOf, num.Integer.toInt_ofInt, hsz]
             rw [hl]
             exact Store.literal_binary_spec s _ _ hokV hinv h64
           · have hl : divLit true (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [divLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_zdiv (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_zdiv, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)

/-- `eo::mod` on handles of two numerals or two binaries: logos's `__eo_zmod`. -/
theorem Store.builtin_spec_int_mod (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IntMod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_zmod x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IntMod 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_zmod Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_zmod; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_zmod x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_zmod; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_zmod x y = Eo.Term.Stuck := by
        unfold Eo.__eo_zmod
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_binary_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have hev := lit_evaluate_int_div false (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2
      simp only [Bool.false_eq_true, ite_false] at hev
      step with hev as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [divLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_zmod] using hinv.rep_stuck⟩)
        | (rw [eo_zmod_num]
           by_cases h0 : i2 = 0
           · simp only [divLit, num.Integer.toInt_ofInt, h0, ite_true, Store.stuck_eq, Std.bind_ok,
               WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
           · simp only [divLit, num.Integer.toInt_ofInt, h0, ite_false, Bool.false_eq_true,
               ite_true]
             exact Store.literal_numeral_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             rw [eo_zmod_bin hok1]
             obtain ⟨hw0, hw1, -, -⟩ := hok1
             have hsz := Tree.u32Wrap_val w1.toNat (by omega)
             have hpos : (0 : Int) < 2 ^ w1.toNat := by positivity
             generalize hV : (if n2 = 0 then _ else _ : Int) = V
             have hokV : Tree.okBv w1 V := by
               refine ⟨hw0, hw1, ?_, ?_⟩ <;> rw [← hV] <;> split_ifs <;>
                 first | exact Int.emod_nonneg _ hpos.ne' | exact Int.emod_lt_of_pos _ hpos
             have hl : divLit false (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Binary (Tree.bvOf w1 V)) := by
               rw [← hV]
               simp [divLit, Tree.bvOf, num.Integer.toInt_ofInt, hsz]
             rw [hl]
             exact Store.literal_binary_spec s _ _ hokV hinv h64
           · have hl : divLit false (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [divLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_zmod (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_zmod, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)


/-! ## `eo::qdiv` -/

/-- `rat_sgn` is zero exactly at zero. -/
theorem rat_sgn_zero (a : num.Rational) :
    ∃ r : Std.I32, lit.rat_sgn a = ok r ∧ (r = 0#i32 ↔ a.toRat = 0) := by
  unfold lit.rat_sgn
  obtain ⟨r, hr, hz⟩ := integer_sgn_zero (num.Integer.ofInt a.toRat.num)
  refine ⟨r, by simp [num.Rational.numerator_spec, hr], ?_⟩
  rw [hz, num.Integer.toInt_ofInt, Rat.num_eq_zero]

/-- `rat_div` of a rational by a nonzero one is the quotient. -/
theorem rat_div_spec (a b : num.Rational) (hb : b.toRat ≠ 0) :
    lit.rat_div a b = ok (num.Rational.ofRat (a.toRat / b.toRat)) := by
  unfold lit.rat_div
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.mul_spec,
    num.Integer.toInt_ofInt, Std.bind_ok]
  have hbn : b.toRat.num ≠ 0 := by rwa [Ne, Rat.num_eq_zero]
  have hd : (a.toRat.den : Int) * b.toRat.num ≠ 0 :=
    mul_ne_zero (by exact_mod_cast a.toRat.den_nz) hbn
  rw [lit_rat_spec _ _ (by rw [num.Integer.toInt_ofInt]; exact hd)]
  congr 1
  simp only [num.Integer.toInt_ofInt]
  push_cast
  conv_rhs => rw [← Rat.num_div_den a.toRat, ← Rat.num_div_den b.toRat]
  have h1 : (a.toRat.den : ℚ) ≠ 0 := by exact_mod_cast a.toRat.den_nz
  have h2 : (b.toRat.den : ℚ) ≠ 0 := by exact_mod_cast b.toRat.den_nz
  have h3 : (b.toRat.num : ℚ) ≠ 0 := by exact_mod_cast hbn
  field_simp

/-- What `Lit::evaluate` gives for `eo::qdiv` on two literals that stand
for terms. -/
noncomputable def ratDivLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral n, lit.Lit.Numeral m =>
    if m.toInt = 0 then none
    else some (lit.Lit.Rational (num.Rational.ofRat ((n.toInt : ℚ) / (m.toInt : ℚ))))
  | lit.Lit.Rational a, lit.Lit.Rational b =>
    if b.toRat = 0 then none
    else some (lit.Lit.Rational (num.Rational.ofRat (a.toRat / b.toRat)))
  | _, _ => none

theorem lit_evaluate_rat_div (args : Slice lit.Lit) {l1 l2 : lit.Lit}
    (hargs : args.val = [l1, l2]) (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.RatDiv args ⦃ o => o = ratDivLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have hl2 : Slice.length args = 2 := by simp [Slice.length, hargs]
  have h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok l2 := by
    intro i hi; simp [Slice.index_usize, hargs, hi]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
  first
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne]
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [ratDivLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [lit.Lit.evaluate_rat_div, lit.Lit.arg, hlen, h1 1#usize (by simp), lit.Lit.as_rat,
       ratDivLit, num.Rational.from_integers_spec]
     all_goals
       rename_i x y
       first
       | (split_ifs <;> simp)
       | (obtain ⟨r, hr, hz⟩ := rat_sgn_zero y
          by_cases h0 : y.toRat = 0
          · simp [hr, hz.mpr h0, h0]
          · have hr0 : ¬ r = 0#i32 := fun h => h0 (hz.mp h)
            simp [hr, hr0, h0, rat_div_spec _ _ h0]))


/-- logos's `eo::qdiv` of two numerals: stuck by zero, else their quotient. -/
theorem eo_qdiv_num (n m : Int) :
    Eo.__eo_qdiv (Eo.Term.Numeral n) (Eo.Term.Numeral m) =
      if m = 0 then Eo.Term.Stuck else Eo.Term.Rational ((n : ℚ) / (m : ℚ)) := by
  by_cases h : m = 0
  · subst h; simp [Eo.__eo_qdiv, SmtEval.native_ite, SmtEval.native_zeq]
  · simp [Eo.__eo_qdiv, SmtEval.native_ite, SmtEval.native_zeq, SmtEval.native_mk_rational, h,
      Ne.symm h]

/-- logos's `eo::qdiv` of two rationals: stuck by zero, else their quotient. -/
theorem eo_qdiv_rat (a b : ℚ) :
    Eo.__eo_qdiv (Eo.Term.Rational a) (Eo.Term.Rational b) =
      if b = 0 then Eo.Term.Stuck else Eo.Term.Rational (a / b) := by
  by_cases h : b = 0
  · subst h; simp [Eo.__eo_qdiv, SmtEval.native_ite, Eo.native_qeq, SmtEval.native_mk_rational]
  · simp [Eo.__eo_qdiv, SmtEval.native_ite, Eo.native_qeq, SmtEval.native_mk_rational,
      SmtEval.native_qdiv_total, h, Ne.symm h]

/-- `eo::qdiv` on handles of two numerals or two rationals: logos's
`__eo_qdiv`. -/
theorem Store.builtin_spec_rat_div (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.RatDiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_qdiv x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.RatDiv 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_qdiv Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_qdiv; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_qdiv x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_qdiv; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_qdiv x y = Eo.Term.Stuck := by
        unfold Eo.__eo_qdiv
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_rational_data ha⟩, ⟨_, Store.rep_rational_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_rat_div (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [ratDivLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_qdiv] using hinv.rep_stuck⟩)
        | (rw [eo_qdiv_num]
           by_cases h0 : i2 = 0
           · simp only [ratDivLit, num.Integer.toInt_ofInt, h0, ite_true, Store.stuck_eq,
               Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
           · simp only [ratDivLit, num.Integer.toInt_ofInt, h0, ite_false]
             exact Store.literal_rational_spec s _ hinv h64)
        | (rw [eo_qdiv_rat]
           by_cases h0 : q2 = 0
           · simp only [ratDivLit, num.Rational.toRat_ofRat, h0, ite_true, Store.stuck_eq,
               Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
           · simp only [ratDivLit, num.Rational.toRat_ofRat, h0, ite_false]
             exact Store.literal_rational_spec s _ hinv h64)

end pathos_compiled_checker
