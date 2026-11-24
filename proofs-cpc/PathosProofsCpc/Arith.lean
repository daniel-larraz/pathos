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

theorem lit_rat_cmp_spec (a b : num.Rational) :
    lit.rat_cmp a b = ok (compare a.toRat b.toRat) := by
  unfold lit.rat_cmp
  simp only [num.Rational.numerator_spec, num.Rational.denominator_spec, num.Integer.mul_spec,
    num.Integer.partial_cmp_spec, num.Integer.toInt_ofInt, Std.bind_ok,
    core.option.Option.unwrap_or]
  congr 1
  rcases lt_trichotomy a.toRat b.toRat with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((Rat.lt_iff ..).mp h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr ((Rat.lt_iff ..).mp h)]

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
-1 for one that is no character (196608 or more), as logos's
`native_str_to_code` (the runtime's check, option (c)). -/
noncomputable def toZStr (e : eostring.EoString) : Option lit.Lit :=
  if e.val.length = 1 then
    some (lit.Lit.Numeral (num.Integer.ofInt
      (if (e.val[0]!).val < 196608 then ((e.val[0]!).val : Int) else -1)))
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
      simp [h1, eostring.EoString.code_points, Slice.index_usize, num_codes_eq,
        num.Integer.from_u32_spec, num.Integer.one_spec, num.Integer.neg_spec,
        num.Integer.toInt_ofInt, alloc.vec.Vec.deref]
      have h0' : (e.val[0]! : Std.U32) = e.val[0] := by
        simp [List.getElem!_eq_getElem?_getD, h1]
      have hu : ∀ h, Usize.ofNatCore 1 h = 1#usize := fun _ => rfl
      by_cases hc : (e.val[0]).val < 196608 <;> simp [hc, h0', hu]
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
                Eo.Term.Numeral (if c < 196608 then (c : Int) else -1) := by
              simp [Eo.__eo_to_z, SmtEval.native_ite, SmtEval.native_zeq, Eo.native_str_len,
                SmtEval.native_str_to_code, SmtEval.native_char_valid]
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

end pathos_compiled_checker
