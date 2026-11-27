module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Runtime.Builtins
public import PathosProofs.Runtime.Strings
public import PathosProofs.Runtime.StringLits
public import PathosProofsCpc.Arith

/-!
# CPC's string builtins (CPC only)

`eo::to_str`, `eo::log` and `eo::find`, as `Lit::evaluate` computes them
on literals, against logos's `__eo_to_str`, `__eo_log` and `__eo_find`.
CPC only, as CpcMini's logos has none of them.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-! ## `eo::to_str` -/

/-- `Lit::evaluate` of `eo::to_str` on one literal: a numeral that is a code
point gives the string of that one character, a string itself. -/
theorem lit_evaluate_to_string (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.ToString args ⦃ o => o = (match l with
      | lit.Lit.Numeral i =>
        if 0 ≤ i.toInt ∧ i.toInt ≤ 196607 then
          some (lit.Lit.Str (Tree.strOf [i.toInt.toNat]))
        else none
      | lit.Lit.Str v => some (lit.Lit.Str v)
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l
  case Numeral i =>
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    obtain ⟨r, hr, hv⟩ := num.Integer.to_u32_spec i
    simp only [lit.Lit.evaluate_to_string, num.Integer.fits_u32_spec, Std.bind_ok]
    by_cases hfit : 0 ≤ i.toInt ∧ i.toInt < 2 ^ 32
    · simp only [hfit, decide_true, ite_true, hr, Std.bind_ok, true_and, and_self] at hv ⊢
      have hle : r ≤ MAX_CODE_POINT ↔ i.toInt ≤ 196607 := by
        rw [max_code_point_eq, ← hv]
        constructor
        · intro h; have := UScalar.le_equiv r 196607#u32 |>.mp h; simp at this; omega
        · intro h; apply (UScalar.le_equiv r 196607#u32).mpr; simp; omega
      by_cases hc : i.toInt ≤ 196607
      · simp only [hle.mpr hc, hc, ite_true]
        simp [Std.Array.to_slice, alloc.slice.Slice.into_vec, eostring.EoString.from_code_points,
          lift, Tree.strOf, Tree.u32Wrap]
        rw [dif_pos (by scalar_tac)]
        apply alloc.vec.Vec.ext
        simp only [alloc.vec.Vec.from_val]
        show [r] = _
        congr 1
        apply UScalar.eq_of_val_eq
        simp only [UScalar.val]
        have h1 : r.val = i.toInt.toNat := by omega
        simp [h1]
        omega
      · simp only [show ¬ r ≤ MAX_CODE_POINT from fun h => hc (hle.mp h), hc, ite_false,
          WP.spec_ok]
    · have hn : ¬ (0 ≤ i.toInt ∧ i.toInt ≤ 196607) := fun h => hfit ⟨h.1, by omega⟩
      have hf : ¬(0 ≤ i.toInt ∧ i.toInt < 4294967296) := by simpa using hfit
      simp [hf, hn]
  all_goals
    simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [lit.Lit.evaluate_to_string, lit_clone_eq]

theorem Store.builtin_spec_to_str (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.ToString args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_to_str x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.ToString 1#usize = ok true := by
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
      have : Eo.__eo_to_str Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_to_str]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_to_str x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_to_str
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
      step with lit_evaluate_to_string (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
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
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_str] using hinv.rep_stuck⟩
        · simp only [num.Integer.toInt_ofInt]
          by_cases hc : 0 ≤ i ∧ i ≤ 196607
          · simp only [hc, and_self, ite_true]
            have hv : Eo.__eo_to_str (Eo.Term.Numeral i) = Eo.Term.String [i.toNat] := by
              simp [Eo.__eo_to_str, SmtEval.native_ite, SmtEval.native_and, SmtEval.native_zleq,
                SmtEval.native_z_max_code_point, SmtEval.native_str_from_code,
                SmtEval.native_char_valid, hc]
            rw [hv]
            obtain ⟨hc1, hc2⟩ := hc
            refine Store.literal_string_spec s _ ⟨by simp; scalar_tac, ?_⟩ hinv h64
            intro c hc'
            simp only [List.mem_singleton] at hc'
            subst hc'
            have h2 : @LE.le Int _ i 196607 := hc2
            rw [show (2 : ℕ) ^ 32 = 4294967296 from rfl]
            omega
          · simp only [hc, ite_false, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv, Store.Grows.refl s, ?_⟩
            have hv : Eo.__eo_to_str (Eo.Term.Numeral i) = Eo.Term.Stuck := by
              simp [Eo.__eo_to_str, SmtEval.native_ite, SmtEval.native_and, SmtEval.native_zleq,
                SmtEval.native_z_max_code_point]
              intro h
              have h' : ¬ @LE.le Int _ i 196607 := fun h2 => hc ⟨h, h2⟩
              exact decide_eq_false h'
            rw [hv]; exact hinv.rep_stuck
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_str] using hinv.rep_stuck⟩
        · simp only
          simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
          have hv : Eo.__eo_to_str (Eo.Term.String str) = Eo.Term.String str := rfl
          rw [hv]
          exact Store.literal_string_spec s _ he hinv h64
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_to_str] using hinv.rep_stuck⟩
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

/-! ## `eo::log` -/

theorem integer_le_spec (a b : num.Integer) :
    core.cmp.PartialOrd.le.trait_default num.Integer.Insts.CoreCmpPartialOrdInteger a b =
      ok (decide (a.toInt ≤ b.toInt)) := by
  simp only [core.cmp.PartialOrd.le.trait_default, core.cmp.PartialOrd.le.default,
    core.cmp.PartialOrd.le_body, num.Integer.partial_cmp_spec, Std.bind_ok]
  congr 1
  rcases lt_trichotomy a.toInt b.toInt with h | h | h
  · simp [compare_lt_iff_lt.mpr h, h.le]
  · simp [compare_eq_iff_eq.mpr h, h]
  · simp [compare_gt_iff_gt.mpr h, not_le.mpr h]

/-- logos's count of divisions is `Nat.log` when the fuel is at least the value. -/
theorem log_rec_eq (b : Nat) (hb : 2 ≤ b) :
    ∀ fuel n : Nat, n ≤ fuel → Eo.impl_native_int_log_rec b fuel n = Nat.log b n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this; simp [Eo.impl_native_int_log_rec]
  | succ f ih =>
    intro n hn
    simp only [Eo.impl_native_int_log_rec]
    by_cases hlt : n < b
    · simp [hlt, Nat.log_of_lt hlt]
    · simp only [hlt, ite_false]
      have hle : b ≤ n := by omega
      have hdiv : n / b ≤ f := by
        have := Nat.div_lt_self (show 0 < n by omega) (show 1 < b by omega); omega
      rw [Nat.log_of_one_lt_of_le (by omega) hle, ih (n / b) hdiv]
      exact Nat.add_comm _ _

/-- The runtime's loop adds `Nat.log` of what remains. -/
theorem floor_log_loop_spec (base res rem : num.Integer) (hb : 2 ≤ base.toInt)
    (hr : 0 ≤ rem.toInt) :
    lit.integer_floor_log_loop base (num.Integer.ofInt 1) res rem =
      ok (num.Integer.ofInt (res.toInt + Nat.log base.toInt.toNat rem.toInt.toNat)) := by
  generalize hn : rem.toInt.toNat = n
  induction n using Nat.strong_induction_on generalizing res rem with
  | _ n ih =>
    rw [lit.integer_floor_log_loop]
    simp only [integer_le_spec, Std.bind_ok]
    by_cases hle : base.toInt ≤ rem.toInt
    · simp only [hle, decide_true, ite_true, num.Integer.add_spec, num.Integer.toInt_ofInt,
        Std.bind_ok]
      rw [num.Integer.euclidean_qr_spec _ _ (by omega)]
      simp only [Std.bind_ok]
      have hq : 0 ≤ rem.toInt / base.toInt := Int.ediv_nonneg hr (by omega)
      have hqn : (rem.toInt / base.toInt).toNat = n / base.toInt.toNat := by
        have hr' : rem.toInt = ((n : Nat) : Int) := by omega
        obtain ⟨bn, hbn⟩ : ∃ bn : Nat, base.toInt = (bn : Int) := ⟨base.toInt.toNat, by omega⟩
        rw [hr', hbn, ← Int.natCast_div, Int.toNat_natCast, Int.toNat_natCast]
      change lit.integer_floor_log_loop base (num.Integer.ofInt 1)
        (num.Integer.ofInt (res.toInt + 1)) (num.Integer.ofInt (rem.toInt / base.toInt)) = _
      rw [ih (n / base.toInt.toNat) (Nat.div_lt_self (by omega) (by omega)) _ _
        (by simp only [num.Integer.toInt_ofInt]; exact hq)
        (by simp only [num.Integer.toInt_ofInt]; exact hqn)]
      congr 2
      simp only [num.Integer.toInt_ofInt]
      rw [Nat.log_of_one_lt_of_le (b := base.toInt.toNat) (n := n) (by omega) (by omega)]
      push_cast; ring
    · simp only [hle, decide_false, Bool.false_eq_true, ite_false]
      rw [Nat.log_of_lt (by omega)]
      simp [num.Integer.ofInt_toInt]

/-- `integer_floor_log` is logos's `native_int_log`. -/
theorem floor_log_spec (base value : num.Integer) :
    lit.integer_floor_log base value =
      ok (num.Integer.ofInt (Eo.native_int_log base.toInt value.toInt)) := by
  unfold lit.integer_floor_log
  simp only [num.Integer.one_spec, integer_le_spec, num.Integer.toInt_ofInt, Std.bind_ok]
  by_cases hb : base.toInt ≤ 1
  · simp only [hb, decide_true, ite_true, num.Integer.zero_spec]
    congr 2
    simp [Eo.native_int_log, show base.toInt.toNat ≤ 1 by omega]
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false]
    obtain ⟨r, hr, hv⟩ := num.Integer.sgn_spec value
    simp only [hr, Std.bind_ok]
    by_cases hv0 : value.toInt ≤ 0
    · have hr0 : r ≤ 0#i32 := by
        have : r.val ≤ 0 := by rw [hv]; exact Int.sign_nonpos_iff.mpr hv0
        exact (IScalar.le_equiv r 0#i32).mpr (by simpa using this)
      simp only [hr0, ite_true, num.Integer.zero_spec]
      congr 2
      simp [Eo.native_int_log, show value.toInt.toNat = 0 by omega]
    · have hr0 : ¬ r ≤ 0#i32 := by
        intro h
        have h' := (IScalar.le_equiv r 0#i32).mp h
        have : r.val = 1 := by rw [hv]; exact Int.sign_eq_one_of_pos (by omega)
        simp [this] at h'
      simp only [hr0, ite_false, num.Integer.zero_spec, num.Integer.clone_spec, Std.bind_ok]
      rw [floor_log_loop_spec _ _ _ (by omega) (by omega)]
      congr 2
      simp only [num.Integer.toInt_ofInt, zero_add]
      have hb2 : 2 ≤ base.toInt.toNat := by omega
      simp only [Eo.native_int_log, show ¬ base.toInt.toNat ≤ 1 by omega,
        show value.toInt.toNat ≠ 0 by omega, decide_false, Bool.false_or, beq_iff_eq,
        Bool.false_eq_true, ite_false]
      rw [log_rec_eq _ hb2 _ _ le_rfl]
      rfl

/-- What `Lit::evaluate` gives for `eo::log` on two literals that stand for
terms: a numeral base and a numeral or rational (rounded down) value. -/
noncomputable def logLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Numeral b, lit.Lit.Numeral v =>
    some (lit.Lit.Numeral (num.Integer.ofInt (Eo.native_int_log b.toInt v.toInt)))
  | lit.Lit.Numeral b, lit.Lit.Rational q =>
    some (lit.Lit.Numeral (num.Integer.ofInt (Eo.native_int_log b.toInt (Rat.floor q.toRat))))
  | _, _ => none

theorem lit_evaluate_log (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Log args ⦃ o => o = logLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok l2 := by simp [Slice.index_usize, hargs]
  have hne : core.slice.Slice.is_empty args = ok false := by
    simp [core.slice.Slice.is_empty, Slice.len, hargs]
  unfold lit.Lit.evaluate
  simp only [hne, h0, Std.bind_ok, Bool.false_eq_true, ite_false, ite_true]
  unfold lit.Lit.evaluate_log
  cases l1 <;> simp only [TermLit] at ht1 <;> simp [lit.Lit.kind, lit.Lit.as_int, logLit]
  cases l2 <;> simp only [TermLit] at ht2 <;>
    simp [logLit, lit.Lit.arg, hlen, h1, floor_log_spec, lit_rat_floor_spec,
      num.Integer.clone_spec, num.Integer.toInt_ofInt]

/-- `eo::log` on handles of two terms: logos's `__eo_log`. -/
theorem Store.builtin_spec_log (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Log args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_log x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Log 2#usize = ok true := by
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
      have : Eo.__eo_log Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_log; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_log x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_log; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_log x y = Eo.Term.Stuck := by
        unfold Eo.__eo_log
        split
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_numeral_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_numeral_data ha⟩, ⟨_, Store.rep_rational_data hb⟩⟩ ho
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
      step with lit_evaluate_log (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [logLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_log] using hinv.rep_stuck⟩)
        | (simp only [logLit, num.Integer.toInt_ofInt, num.Rational.toRat_ofRat]
           exact Store.literal_numeral_spec s _ hinv h64)

/-! ## `eo::find` -/

/-- logos's prefix test is `isPrefixOf`. -/
theorem smt_prefix_eq_isPrefixOf (a b : List Nat) :
    SmtEval.native_string_prefix_eq a b = a.isPrefixOf b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons c cs ih =>
    cases b with
    | nil => rfl
    | cons d ds =>
      simp only [SmtEval.native_string_prefix_eq, List.isPrefixOf, ih]
      cases h : decide (c = d) <;> simp_all

/-- Code points as numbers: one list is a prefix of the other exactly when it
is as `u32`s. -/
theorem isPrefixOf_map_val (a b : List Std.U32) :
    (a.map (fun c => c.val)).isPrefixOf (b.map (fun c => c.val)) = a.isPrefixOf b := by
  induction a generalizing b with
  | nil => rfl
  | cons c cs ih =>
    cases b with
    | nil => rfl
    | cons d ds =>
      have hw : (c.val == d.val) = (c == d) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩
      simp only [List.map_cons, List.isPrefixOf, hw, ih]

/-- `occurs_at`'s loop from `i` on: whether the rest of `y` from `i` is a
prefix of `x` from `at + i`, and `same`. -/
theorem occurs_at_loop_spec (x y : Slice Std.U32) (at' : Std.Usize)
    (hat : at'.val + y.length ≤ x.length) :
    ∀ (same : Bool) (i : Std.Usize), i.val ≤ y.length →
      eostring.occurs_at_loop x y at' same i ⦃ r =>
        r = (same && (y.val.drop i.val).isPrefixOf (x.val.drop (at'.val + i.val))) ⦄ := by
  intro same i hi
  generalize hn : y.length - i.val = n
  induction n using Nat.strong_induction_on generalizing same i with
  | _ n ih =>
    rw [eostring.occurs_at_loop]
    split
    · rename_i hlt
      have hlt' : i.val < y.length := by scalar_tac
      have hx' : at'.val + i.val < x.length := by omega
      step as ⟨j, hj⟩
      step as ⟨c, hc⟩
      step as ⟨d, hd⟩
      have hdy : y.val.drop i.val = d :: y.val.drop (i.val + 1) := by
        rw [hd]; exact List.drop_eq_getElem_cons hlt'
      have hdx : x.val.drop (at'.val + i.val) = c :: x.val.drop (at'.val + i.val + 1) := by
        rw [hc, List.drop_eq_getElem_cons hx']; simp [hj]
      rw [hdy, hdx]
      split
      · rename_i hne
        step as ⟨k, hk⟩
        apply WP.spec_mono (ih (y.length - k.val) (by omega) false k (by omega) rfl)
        intro r hr
        have hne' : c ≠ d := by simpa using hne
        have hcd : (d == c) = false := beq_false_of_ne (Ne.symm hne')
        simp [hr, List.isPrefixOf, hcd]
      · rename_i heq
        step as ⟨k, hk⟩
        apply WP.spec_mono (ih (y.length - k.val) (by omega) same k (by omega) rfl)
        intro r hr
        have hcd : d = c := by
          have : c.val = d.val := by simpa using heq
          exact (UScalar.eq_of_val_eq this).symm
        rw [hr, show at'.val + k.val = at'.val + i.val + 1 by omega,
          show k.val = i.val + 1 by omega]
        simp [List.isPrefixOf, hcd]
    · rename_i hge
      have : y.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      simp [this]

/-- `find`'s answer as logos writes it: an index, or `-1` for none. -/
def optIdx : Option Std.Usize → Int
  | none => -1
  | some j => j.val

/-- `find`'s loop from `i` on, while nothing has been found: logos's search
with the fuel of the positions left. Once found, `i` is past `last`. -/
theorem find_loop_spec (self y : eostring.EoString) (last : Std.Usize)
    (hlast : last.val + y.val.length = self.val.length) (hy : 0 < y.val.length) :
    ∀ (found : Option Std.Usize) (i : Std.Usize), (found = none ∨ i.val = last.val + 1) →
      i.val ≤ last.val + 1 →
      eostring.EoString.find_loop self y last found i ⦃ r =>
        optIdx r = match found with
          | none => Eo.impl_native_str_indexof_rec (self.val.map (fun c => c.val))
              (y.val.map (fun c => c.val)) i.val (last.val + 1 - i.val)
          | some j => j.val ⦄ := by
  have hmax : self.val.length ≤ Usize.max := self.property
  intro found i hf hi
  generalize hn : last.val + 1 - i.val = n
  induction n using Nat.strong_induction_on generalizing found i with
  | _ n ih =>
    rw [eostring.EoString.find_loop]
    split
    · rename_i hle
      have hle' : i.val ≤ last.val := by scalar_tac
      have hf' : found = none := by
        rcases hf with h | h
        · exact h
        · omega
      subst hf'
      simp only [eostring.occurs_at]
      step with occurs_at_loop_spec (alloc.vec.Vec.deref self) (alloc.vec.Vec.deref y) i
        (by simp [alloc.vec.Vec.deref, Slice.length]; omega) true 0#usize (by simp)
        as ⟨b, hb⟩
      have hrec : Eo.impl_native_str_indexof_rec (self.val.map (fun c => c.val))
          (y.val.map (fun c => c.val)) i.val n =
          if b then (i.val : Int) else
            Eo.impl_native_str_indexof_rec (self.val.map (fun c => c.val))
              (y.val.map (fun c => c.val)) (i.val + 1) (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [Eo.impl_native_str_indexof_rec, smt_prefix_eq_isPrefixOf, ← List.map_drop,
          isPrefixOf_map_val, hb]
        simp [alloc.vec.Vec.deref]
      split
      · rename_i hbt
        step as ⟨k, hk⟩
        apply WP.spec_mono (ih 0 (by omega) (some i) k (Or.inr (by omega)) (by omega) (by omega))
        intro r hr
        simp only at hr
        rw [hr, hrec, hbt]; rfl
      · rename_i hbf
        step as ⟨k, hk⟩
        apply WP.spec_mono (ih (n - 1) (by omega) none k (Or.inl rfl) (by omega) (by omega))
        intro r hr
        simp only at hr
        rw [hr, hrec, show k.val = i.val + 1 by omega]
        simp [hbf]
    · rename_i hgt
      have hgt' : i.val = last.val + 1 := by scalar_tac
      have h0 : n = 0 := by omega
      subst h0
      cases found <;> simp [optIdx, Eo.impl_native_str_indexof_rec]

/-- `EoString::find` is logos's `native_str_indexof` from `0`. -/
theorem find_spec (self y : eostring.EoString) :
    eostring.EoString.find self y ⦃ r =>
      optIdx r = Eo.native_str_indexof (self.val.map (fun c => c.val))
        (y.val.map (fun c => c.val)) 0 ⦄ := by
  unfold eostring.EoString.find
  simp only [eostring.EoString.len, eostring.EoString.is_empty, alloc.vec.Vec.is_empty,
    Std.bind_ok]
  split
  · rename_i hlt
    have hlt' : self.val.length < y.val.length := by scalar_tac
    simp [optIdx, Eo.native_str_indexof, Eo.native_str_len]
    omega
  · rename_i hge
    have hge' : y.val.length ≤ self.val.length := by scalar_tac
    split
    · rename_i hemp
      have hy0 : y.val = [] := by
        simpa [alloc.vec.Vec.len] using hemp
      simp [optIdx, Eo.native_str_indexof, Eo.native_str_len, hy0,
        Eo.impl_native_str_indexof_rec, smt_prefix_eq_isPrefixOf]
    · rename_i hemp
      have hy0 : 0 < y.val.length := by
        cases h : y.val with
        | nil => simp [alloc.vec.Vec.len, h] at hemp
        | cons _ _ => simp
      step as ⟨last, hl⟩
      apply WP.spec_mono (find_loop_spec self y last (by scalar_tac) hy0 none 0#usize
        (Or.inl rfl) (by simp))
      intro r hr
      have hlv : last.val = self.val.length - y.val.length := by scalar_tac
      rw [hr]
      simp [Eo.native_str_indexof, Eo.native_str_len, hge', hlv]

/-- What `Lit::evaluate` gives for `eo::find` on two literals that stand for
terms: on two strings, logos's index of the second in the first. -/
noncomputable def findLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Str a, lit.Lit.Str b =>
    some (lit.Lit.Numeral (num.Integer.ofInt
      (Eo.native_str_indexof (a.val.map (fun c => c.val)) (b.val.map (fun c => c.val)) 0)))
  | _, _ => none

theorem lit_evaluate_find (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.Find args ⦃ o => o = findLit l1 l2 ⦄ := by
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
     simp [findLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     first
     | (simp [lit.Lit.as_str, findLit]; done)
     | (simp only [lit.Lit.as_str, lit.Lit.str_arg, lit.Lit.arg, hlen, h1 1#usize (by simp),
          Std.bind_ok, ite_true, show (1#usize : Std.Usize) < 2#usize by decide]
        step with find_spec as ⟨r, hr⟩
        cases r <;> simp only [optIdx] at hr <;>
          simp [findLit, ← hr, num.Integer.one_spec, num.Integer.neg_spec,
            num.Integer.toInt_ofInt, num.Integer.from_usize_spec]))

theorem Store.rep_string_data {s : Store} {a : Term} {str : List Nat}
    (ha : s.Rep a (Eo.Term.String str)) :
    s.nodes.val[a.val]! = TermData.Literal (lit.Lit.Str (Tree.strOf str)) := by
  obtain ⟨hh, _⟩ := ha
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
  cases hh with
  | lit _ _ _ hd => exact hd

/-- The characters of a string term the store holds are those of its literal. -/
theorem Store.rep_string_chars {s : Store} {a : Term} {str : List Nat}
    (ha : s.Rep a (Eo.Term.String str)) :
    (Tree.strOf str).val.map (fun c => c.val) = str := by
  have he := ha.2
  simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
  rw [Tree.strOf_val _ he, Tree.u32Wrap_val_of _ he]

/-- `eo::find` on handles of two terms: logos's `__eo_find`. -/
theorem Store.builtin_spec_find (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Find args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_find x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Find 2#usize = ok true := by
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
      have : Eo.__eo_find Eo.Term.Stuck y = Eo.Term.Stuck := by
        unfold Eo.__eo_find; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_find x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_find; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_find x y = Eo.Term.Stuck := by
        unfold Eo.__eo_find
        split
        · exact absurd ⟨⟨_, Store.rep_string_data ha⟩, ⟨_, Store.rep_string_data hb⟩⟩ ho
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
      step with lit_evaluate_find (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [findLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_find] using hinv.rep_stuck⟩)
        | (simp only [findLit, Store.rep_string_chars ha, Store.rep_string_chars hb]
           exact Store.literal_numeral_spec s _ hinv h64)

end pathos_compiled_checker
