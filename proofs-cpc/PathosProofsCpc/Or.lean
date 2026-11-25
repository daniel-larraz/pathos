module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Runtime.Builtins

/-!
# `eo::or` (CPC only)

`eo::or` of two Booleans or of two binaries of the same width, which
CpcMini's logos does not define, so the shared library cannot state it
(milestone 6, option (b)). The proofs follow `eo::and`'s in
PathosProofs/Runtime/Builtins.lean, with `||`, `Int.lor` and logos's
`impl_native_pior`.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- What `Lit::evaluate` gives for `eo::or` on two literals that stand for
terms. -/
noncomputable def orLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Boolean b1, lit.Lit.Boolean b2 => some (lit.Lit.Boolean (b1 || b2))
  | lit.Lit.Binary c1, lit.Lit.Binary c2 =>
    if c1.size = c2.size then
      some (lit.Lit.Binary ⟨c1.size, num.Integer.ofInt
        (Int.emod (Int.lor c1.value.toInt c2.value.toInt) (2 ^ c1.size.val))⟩)
    else none
  | _, _ => none

theorem fold_bool_or (args : Slice lit.Lit) (b1 b2 : Bool) (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Boolean b2)) :
    lit.Lit.fold_bool kind.EvalOp.Or b1 args ⦃ o => o = some (lit.Lit.Boolean (b1 || b2)) ⦄ := by
  unfold lit.Lit.fold_bool lit.Lit.fold_bool_loop
  cases b1 <;>
  · simp [hlen, h1 1#usize (by simp), lit.Lit.as_bool]
    step as ⟨j, hj⟩
    unfold lit.Lit.fold_bool_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp [hlen, hj2]

theorem fold_bv_or (args : Slice lit.Lit) (c1 c2 : bitvec.BitVec)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Binary c2)) :
    lit.Lit.fold_bv kind.EvalOp.Or kind.LitKind.Binary c1 args ⦃ o =>
      o = orLit (lit.Lit.Binary c1) (lit.Lit.Binary c2) ⦄ := by
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
      core.clone.impls.CloneU32.clone, num.Integer.clone_spec, bitvec.BitVec.or,
      bitvec.BitVec.new, num.Integer.bitwise_or_spec, num.Integer.mod_by_pow2_spec]
    step as ⟨k, hk⟩
    subst hk
    step as ⟨k2, hk2⟩
    have hk3 : ¬ (k2.val ≤ 1) := by scalar_tac
    simp [hk3, num.Integer.toInt_ofInt, lit.Lit.bitvec, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant, orLit, hs]
    unfold lit.Lit.fold_bv_loop1
    have hk4 : ¬ k2 < 2#usize := by scalar_tac
    simp [hlen, hk4]
  · simp only [hs, ite_false, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp [hlen, hj2, orLit, Ne.symm hs]

theorem lit_evaluate_or (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Or args ⦃ o => o = orLit l1 l2 ⦄ := by
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
     simp [orLit]
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
     | (simp [lit.Lit.fold_str, orLit]; done)
     | exact fold_bool_or args _ _ hlen h1
     | exact fold_bv_or args _ _ hlen h1
     | (unfold lit.Lit.fold_int lit.Lit.fold_int_loop
        simp [hlen, h1 1#usize (by simp), lit.Lit.as_int, num.Integer.clone_spec]
        step as ⟨j, hj⟩
        unfold lit.Lit.fold_int_loop
        have hj2 : ¬ j < 2#usize := by scalar_tac
        simp [hlen, hj2, orLit])
     | (unfold lit.Lit.fold_rat lit.Lit.fold_rat_loop
        simp [hlen, h1 1#usize (by simp), lit.Lit.as_rat, num.Rational.clone_spec]
        step as ⟨j, hj⟩
        unfold lit.Lit.fold_rat_loop
        have hj2 : ¬ j < 2#usize := by scalar_tac
        simp [hlen, hj2, orLit]))

/-- The signed value of the `or` of two bit-vectors of width `k`, reduced
modulo `2 ^ k`, is the `or` of their values: logos's `native_pior` takes
`BitVec.toInt`, which is negative where the top bit is set, and the
reduction makes it agree with malachite's `or` of the values. -/
theorem bv_or_toInt_emod (k : Nat) (n1 n2 : Int) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2)
    (h1' : n1 < 2 ^ k) (h2' : n2 < 2 ^ k) :
    ((BitVec.ofInt k n1 ||| BitVec.ofInt k n2).toInt) % (2 ^ k : Int) =
      Int.lor n1 n2 % (2 ^ k) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  have ha : a < 2 ^ k := by exact_mod_cast h1'
  have hb : b < 2 ^ k := by exact_mod_cast h2'
  rw [BitVec.toInt_eq_toNat_cond]
  have hn : (BitVec.ofInt k (a : Int) ||| BitVec.ofInt k (b : Int)).toNat = a ||| b := by
    rw [BitVec.toNat_or]
    have e1 : (BitVec.ofInt k (a : Int)).toNat = a := by
      rw [show (a : Int) = ((a : Nat) : Int) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt ha
    have e2 : (BitVec.ofInt k (b : Int)).toNat = b := by
      rw [show (b : Int) = ((b : Nat) : Int) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hb
    rw [e1, e2]
  rw [hn]
  have hl : Int.lor (a : Int) (b : Int) = ((a ||| b : Nat) : Int) := rfl
  rw [hl]
  split
  · rfl
  · push_cast
    rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- `eo::or` of two binaries of the same width, as the runtime computes
it. -/
theorem eo_or_binary (w n1 n2 : Int) (h1 : Tree.okBv w n1) (h2 : Tree.okBv w n2) :
    Eo.__eo_or (Eo.Term.Binary w n1) (Eo.Term.Binary w n2) =
      Eo.Term.Binary w (Int.lor n1 n2 % 2 ^ w.toNat) ∧
    Tree.okBv w (Int.lor n1 n2 % 2 ^ w.toNat) := by
  obtain ⟨hw0, hw1, hn1, hn1'⟩ := h1
  obtain ⟨-, -, hn2, hn2'⟩ := h2
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  refine ⟨?_, hw0, hw1, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  have hv : SmtEval.native_mod_total (SmtEval.native_binary_or w n1 n2) (SmtEval.native_int_pow2 w) =
      Int.lor n1 n2 % 2 ^ w.toNat := by
    have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
      simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
    rw [hp]
    simp only [SmtEval.native_mod_total, SmtEval.native_binary_or, SmtEval.native_ite,
      SmtEval.native_zeq, SmtEval.impl_native_pior]
    by_cases hw : w = 0
    · subst hw
      simp
    · simp only [hw, decide_false]
      exact bv_or_toInt_emod w.toNat n1 n2 hn1 hn2 hn1' hn2'
  simp [Eo.__eo_or, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not, hv]

theorem Store.builtin_spec_or (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Or args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_or x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Or 2#usize = ok true := by
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
      have : Eo.__eo_or Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_or]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_or x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_or; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_or x y = Eo.Term.Stuck := by
        unfold Eo.__eo_or
        split
        · exact absurd ⟨⟨_, Store.rep_boolean_data ha⟩, ⟨_, Store.rep_boolean_data hb⟩⟩ ho
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
      step with lit_evaluate_or (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [orLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_or] using hinv.rep_stuck⟩)
        | (simp only [orLit]
           have he : Eo.__eo_or (Eo.Term.Boolean b1) (Eo.Term.Boolean b2) =
               Eo.Term.Boolean (b1 || b2) := rfl
           rw [he]
           exact Store.literal_boolean_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             obtain ⟨he, hok⟩ := eo_or_binary w1 n1 n2 hok1 hok2
             rw [he]
             have hl : orLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Binary (Tree.bvOf w1 (Int.lor n1 n2 % 2 ^ w1.toNat))) := by
               have hs := Tree.u32Wrap_val w1.toNat (by obtain ⟨_, h, _⟩ := hok1; omega)
               simp [orLit, Tree.bvOf, num.Integer.toInt_ofInt, hs]
               rfl
             rw [hl]
             exact Store.literal_binary_spec s _ _ hok hinv h64
           · have hl : orLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [orLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_or (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_or, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)

end pathos_compiled_checker
