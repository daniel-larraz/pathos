module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtTranslate
import all CpcMini.SmtTyping
import all CpcMini.SmtTranslate
public import PathosProofs.Util
public import PathosProofs.Eunoia.Natives
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Natives
public import PathosProofs.Runtime.Strings
public import PathosProofs.Runtime.Nats
public import PathosProofs.Runtime.Numbers

/-!
# The native operations on integers

`native_op` on integer arguments reads each argument's numeral (`raw_int`:
a clone of the `Integer`) and computes with the functions of `num.rs`:
comparisons (`==`, and `<=`/`<` through `partial_cmp`), `mod_total`
(the Euclidean remainder, or the dividend for a zero divisor),
`int_pow2` (`2^n`, 0 for a negative `n`, an error past `u32`), `int.to_nat`
and `nat.succ`. Each is what logos's native function computes.

These rest on `Trusted.lean`'s specs of `clone`, `eq`, `partial_cmp`,
`sgn`, `zero`, `one`, `add`, `euclidean_qr`, `fits_u32`, `to_u32`, `from`
of a `u32` and `pow`: what malachite computes, through `num.rs`.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `raw_int` on the handle of a native numeral: a copy of the numeral. -/
theorem Store.raw_int_of {s : Store} {t : Term} {i : num.Integer}
    (hlt : t.val < s.nodes.length)
    (hd : s.nodes.val[t.val]! = TermData.Native (lit.Lit.Numeral i)) :
    Store.raw_int s t = ok (core.result.Result.Ok i) := by
  unfold Store.raw_int
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hd,
    num.Integer.clone_spec]

/-- `raw_int` on a handle of an integer. -/
theorem Store.raw_int_rep {s : Store} {t : Term} {x : Int} (h : Represents.rep s t x) :
    Store.raw_int s t = ok (core.result.Result.Ok (num.Integer.ofInt x)) := by
  obtain ⟨hlt, hd⟩ := Store.rep_native_data (l := lit.Lit.Numeral (num.Integer.ofInt x)) h rfl
  exact Store.raw_int_of hlt hd

/-- `raw_int` on a handle of a natural number. -/
theorem Store.raw_int_rep_nat {s : Store} {t : Term} {x : Nat} (h : Represents.rep s t x) :
    Store.raw_int s t = ok (core.result.Result.Ok (num.Integer.ofInt x)) := by
  obtain ⟨hlt, hd⟩ := Store.rep_nat_data h
  exact Store.raw_int_of hlt hd

/-- The three signs of an integer. -/
theorem int_sign_cases (x : Int) :
    (x < 0 ∧ Int.sign x = -1) ∨ (x = 0 ∧ Int.sign x = 0) ∨ (0 < x ∧ Int.sign x = 1) := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inl ⟨h, Int.sign_eq_neg_one_of_neg h⟩
  · exact Or.inr (Or.inl ⟨h, by simp [h]⟩)
  · exact Or.inr (Or.inr ⟨h, Int.sign_eq_one_of_pos h⟩)

/-! ## Numeral constants

The generated code builds a numeral constant as `Integer::from(<n>u32)`,
negated for a negative one (`.neg()`); after the specs of `from` and
`neg`, the store is given `ofInt` of the `u32`'s value. -/

theorem Store.raw_int_u32_spec (s : Store) (n : Std.U32) (i : Int) (hi : (n.val : Int) = i)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Numeral (num.Integer.ofInt (n.val : Int))) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t i
      | core.result.Result.Err _ => True ⦄div := by
  rw [hi]; exact Store.raw_int_spec s i hinv h64

theorem Store.raw_int_neg_u32_spec (s : Store) (n : Std.U32) (i : Int)
    (hi : -(n.val : Int) = i) (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Numeral (num.Integer.ofInt (-(n.val : Int)))) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t i
      | core.result.Result.Err _ => True ⦄div := by
  rw [hi]; exact Store.raw_int_spec s i hinv h64

/-! ## Comparisons -/

theorem Store.native_spec_zeq (s : Store) (args : Slice Term) {a b : Term} {x y : Int}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Zeq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_zeq x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_int_compare
  simp only [Store.raw_int_rep ha, Store.raw_int_rep hb, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, num.Integer.eq_spec, num.Integer.toInt_ofInt]
  exact Store.native_bool_spec s _ hinv h64

theorem Store.native_spec_zleq (s : Store) (args : Slice Term) {a b : Term} {x y : Int}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Zleq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_zleq x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_int_compare
  simp only [Store.raw_int_rep ha, Store.raw_int_rep hb, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, core.cmp.PartialOrd.le.trait_default,
    core.cmp.PartialOrd.le.default, core.cmp.PartialOrd.le_body,
    num.Integer.partial_cmp_spec, num.Integer.toInt_ofInt]
  convert Store.native_bool_spec s (Eunoia.native_zleq x y) hinv h64 using 3
  simp [Eunoia.native_zleq, compare_lt_iff_lt, compare_eq_iff_eq, le_iff_lt_or_eq]

/-! ## Arithmetic -/

theorem Store.native_spec_mod_total (s : Store) (args : Slice Term) {a b : Term} {x y : Int}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.ModTotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_mod_total x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_int_binary
  simp only [Store.raw_int_rep ha, Store.raw_int_rep hb, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec (num.Integer.ofInt y)
  rw [num.Integer.toInt_ofInt] at hsv
  rw [hsg]
  simp only [Std.bind_ok]
  by_cases hy : y = 0
  · subst hy
    have : sg = 0#i32 := by
      apply IScalar.eq_of_val_eq
      rw [hsv]; rfl
    simp only [this, ite_true, Std.bind_ok]
    have hv : Eunoia.native_mod_total x 0 = x := by simp [Eunoia.native_mod_total]
    rw [hv]
    exact Store.raw_int_spec s x hinv h64
  · have : sg ≠ 0#i32 := by
      intro h0; subst h0
      rcases int_sign_cases y with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩
      · rw [h] at hsv; scalar_tac
      · exact hy h
      · rw [h] at hsv; scalar_tac
    simp only [this, ite_false, num.Integer.euclidean_qr_spec _ _
      (by rw [num.Integer.toInt_ofInt]; exact hy), num.Integer.toInt_ofInt, Std.bind_ok]
    have hv : Eunoia.native_mod_total x y = x % y := rfl
    rw [hv]
    simp
    exact Store.raw_int_spec s (x % y) hinv h64

theorem Store.native_spec_int_pow2 (s : Store) (args : Slice Term) {a : Term} {x : Int}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.IntPow2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_int_pow2 x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_pow2
  simp only [Store.raw_int_rep ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec (num.Integer.ofInt x)
  rw [num.Integer.toInt_ofInt] at hsv
  rw [hsg]
  simp only [Std.bind_ok]
  by_cases hx : x < 0
  · have : sg < 0#i32 := by
      have : sg.val = -1 := by rw [hsv]; exact Int.sign_eq_neg_one_of_neg hx
      scalar_tac
    simp only [this, ite_true, num.Integer.zero_spec, Std.bind_ok]
    have hv : Eunoia.native_int_pow2 x = 0 := by
      simp [Eunoia.native_int_pow2, Eunoia.native_zexp_total, hx]
    rw [hv]
    exact Store.raw_int_spec s 0 hinv h64
  · have : ¬ sg < 0#i32 := by
      intro hlt
      have : sg.val < 0 := by scalar_tac
      rcases int_sign_cases x with ⟨h1, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · exact hx h1
      · rw [h] at hsv; omega
      · rw [h] at hsv; omega
    simp only [this, ite_false, num.Integer.fits_u32_spec, num.Integer.toInt_ofInt]
    by_cases hf : 0 ≤ x ∧ x < 2 ^ 32
    · simp only [hf, decide_true, ite_true, num.Integer.from_u32_spec, Std.bind_ok]
      obtain ⟨u, hu, huv⟩ := num.Integer.to_u32_spec (num.Integer.ofInt x)
      rw [num.Integer.toInt_ofInt] at huv
      rw [hu]
      simp only [Std.bind_ok, num.Integer.pow_spec, num.Integer.toInt_ofInt]
      have hux : (u.val : Int) = x := by rw [huv]; simp only [hf, and_self, ite_true]
      have hpow : ((2#u32).val : Int) ^ u.val = Eunoia.native_int_pow2 x := by
        simp only [Eunoia.native_int_pow2, Eunoia.native_zexp_total, hx, ite_false]
        have : u.val = x.toNat := by omega
        rw [this]; simp
      rw [hpow]
      exact Store.raw_int_spec s _ hinv h64
    · simp only [hf, decide_false, Bool.false_eq_true, ite_false, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, trivial⟩

/-! ## Natural numbers -/

theorem Store.native_spec_int_to_nat (s : Store) (args : Slice Term) {a : Term} {x : Int}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.IntToNat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_int_to_nat x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_int_to_nat
  simp only [Store.raw_int_rep ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec (num.Integer.ofInt x)
  rw [num.Integer.toInt_ofInt] at hsv
  rw [hsg]
  simp only [Std.bind_ok]
  by_cases hx : x < 0
  · have : sg < 0#i32 := by
      have : sg.val = -1 := by rw [hsv]; exact Int.sign_eq_neg_one_of_neg hx
      scalar_tac
    simp only [this, ite_true, num.Integer.zero_spec, Std.bind_ok]
    have h0' : Eunoia.native_int_to_nat x = 0 := by
      simp [Eunoia.native_int_to_nat]; omega
    rw [h0']
    have := Store.raw_nat_spec s 0 hinv h64
    simp only [Nat.cast_zero] at this
    exact this
  · have : ¬ sg < 0#i32 := by
      intro hlt
      have : sg.val < 0 := by scalar_tac
      rcases int_sign_cases x with ⟨h1, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · exact hx h1
      · rw [h] at hsv; omega
      · rw [h] at hsv; omega
    simp only [this, ite_false]
    have := Store.raw_nat_spec s (Eunoia.native_int_to_nat x) hinv h64
    have hc : ((Eunoia.native_int_to_nat x : Nat) : Int) = x := by
      simp [Eunoia.native_int_to_nat]; omega
    rw [hc] at this
    exact this

theorem Store.native_spec_nat_succ (s : Store) (args : Slice Term) {a : Term} {x : Nat}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.NatSucc args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Nat.succ x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_succ
  simp only [Store.raw_int_rep_nat ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    num.Integer.one_spec, num.Integer.add_spec, num.Integer.toInt_ofInt]
  have := Store.raw_nat_spec s (x + 1) hinv h64
  push_cast at this
  exact this

/-! ## More of CPC's natives -/

theorem Store.native_spec_zplus (s : Store) (args : Slice Term) {a b : Term} {x y : Int}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Zplus args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_zplus x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_int_binary
  simp only [Store.raw_int_rep ha, Store.raw_int_rep hb, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, num.Integer.add_spec, num.Integer.toInt_ofInt]
  exact Store.raw_int_spec s (x + y) hinv h64

theorem Store.native_spec_nateq (s : Store) (args : Slice Term) {a b : Term} {x y : Nat}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Nateq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_nateq x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_int_compare
  simp only [Store.raw_int_rep_nat ha, Store.raw_int_rep_nat hb, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, num.Integer.eq_spec, num.Integer.toInt_ofInt]
  convert Store.native_bool_spec s (Eunoia.native_nateq x y) hinv h64 using 3
  simp [Eunoia.native_nateq]

/-- `nat.to_int` gives its argument's handle: a natural and an integer are
stored alike (`encNat`, `encInt`). -/
theorem Store.native_spec_nat_to_int (s : Store) (args : Slice Term) {a : Term} {x : Nat}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.NatToInt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_nat_to_int x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_nat_to_int
  simp only [Store.raw_int_rep_nat ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    WP.dspec_ok, WP.uncurry'_pair]
  exact ⟨hinv, Store.Grows.refl s, ha.1, trivial⟩

theorem Store.native_spec_zlt (s : Store) (args : Slice Term) {a b : Term} {x y : Int}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Zlt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_zlt x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_int_compare
  simp only [Store.raw_int_rep ha, Store.raw_int_rep hb, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, core.cmp.PartialOrd.lt.trait_default,
    core.cmp.PartialOrd.lt.default, core.cmp.PartialOrd.lt_body,
    num.Integer.partial_cmp_spec, num.Integer.toInt_ofInt]
  convert Store.native_bool_spec s (Eunoia.native_zlt x y) hinv h64 using 3
  simp [Eunoia.native_zlt, compare_lt_iff_lt]

theorem Store.native_spec_zneg (s : Store) (args : Slice Term) {a : Term} {x : Int}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Zneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_zneg x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_int_unary
  have hz : native.NativeOp.Insts.CoreCmpPartialEqNativeOp.eq native.NativeOp.Zneg
      native.NativeOp.Zneg = ok true := by
    simp [native.NativeOp.Insts.CoreCmpPartialEqNativeOp.eq]
  simp only [Store.raw_int_rep ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hz,
    ite_true, num.Integer.neg_spec, num.Integer.toInt_ofInt]
  exact Store.raw_int_spec s (-x) hinv h64

end pathos_compiled_checker
