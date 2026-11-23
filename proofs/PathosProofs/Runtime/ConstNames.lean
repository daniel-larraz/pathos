module
public import MiniChecker
public import CpcMini.Logos
public import CpcMini.SmtTranslate
import all CpcMini.SmtTyping
import all CpcMini.SmtEval
import all Init.Data.Repr
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Strings
public import PathosProofs.Runtime.StringLits
public import PathosProofs.Runtime.IntNatives

/-!
# The names of constants (`native::constant_name`)

logos's `native_uconst_id i` is `"@u." ++ toString i`. The runtime builds
that name from the decimal digits (`native::decimal_digits`, repeated
`euclidean_qr` by 10, the last digit first, then copied back to front), so
that its translation is proved to spell it here, with the specs of
`euclidean_qr`, `to_u32`, `sgn`, `from_u32` and `clone` that are already in
use. (It used `format!`, which was trusted to return and nothing more.)

The runtime gives an error, not a name, for a number with more digits than
a vector of code points can hold (`MAX_NAME_DIGITS`); no store can hold
such a name, and no number that large can be held in memory either.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-! ## The digits -/

/-- The decimal digits of `m` as code points, the last first. -/
def digitsRev (m : Nat) : List Nat :=
  (48 + m % 10) :: (if m / 10 = 0 then [] else digitsRev (m / 10))
termination_by m
decreasing_by omega

theorem digitsRev_eq (m : Nat) :
    digitsRev m = (48 + m % 10) :: (if m / 10 = 0 then [] else digitsRev (m / 10)) := by
  rw [digitsRev]

theorem digitChar_toNat (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat = 48 + d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem toDigitsCore_map (f : Nat) :
    ∀ (n : Nat) (ds : List Char), n < f →
      (Nat.toDigitsCore 10 f n ds).map Char.toNat = (digitsRev n).reverse ++ ds.map Char.toNat := by
  induction f with
  | zero => intro n ds h; omega
  | succ f ih =>
    intro n ds h
    unfold Nat.toDigitsCore
    simp only
    rw [digitsRev_eq n]
    split
    · rename_i h0
      simp [h0, digitChar_toNat _ (Nat.mod_lt _ (by decide))]
    · rename_i h0
      rw [ih (n / 10) _ (by omega)]
      simp [h0, digitChar_toNat _ (Nat.mod_lt _ (by decide))]

/-- The code points of the decimal numeral of `n`. -/
theorem toString_codes (n : Nat) :
    (toString n).toList.map Char.toNat = (digitsRev n).reverse := by
  show (Nat.repr n).toList.map Char.toNat = _
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList, toDigitsCore_map (n + 1) n [] (by omega)]
  simp

/-- logos's name of the `i`-th uninterpreted constant. -/
theorem native_uconst_id_codes (i : Nat) :
    Smtm.native_uconst_id i = [64, 117, 46] ++ (digitsRev i).reverse := by
  unfold Smtm.native_uconst_id SmtEval.native_string_lit
  dsimp only
  rw [toString_codes]
  rfl

/-! ## The runtime's loops -/

/-- The digit loop: on `m ≥ 0`, the digits so far and then `m`'s, the last
first, or an error where there would be too many. -/
theorem decimal_digits_loop_spec (ten : num.Integer) (hten : ten = num.Integer.ofInt 10) :
    ∀ (digits : alloc.vec.Vec Std.U32) (m : num.Integer) (k : Nat), m.toInt = k →
      digits.val.length ≤ Usize.max - 8 →
      native.decimal_digits_loop ten digits m ⦃ r =>
        match r with
        | core.result.Result.Ok ds => ds.val.map (fun c => c.val) =
            digits.val.map (fun c => c.val) ++ digitsRev k ∧ ds.val.length ≤ Usize.max - 8
        | core.result.Result.Err _ => True ⦄div := by
  apply native.decimal_digits_loop.fixpoint_induct ten
    (motive := fun loop => ∀ (digits : alloc.vec.Vec Std.U32) (m : num.Integer) (k : Nat),
      m.toInt = k → digits.val.length ≤ Usize.max - 8 →
      loop digits m ⦃ r =>
        match r with
        | core.result.Result.Ok ds => ds.val.map (fun c => c.val) =
            digits.val.map (fun c => c.val) ++ digitsRev k ∧ ds.val.length ≤ Usize.max - 8
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih digits m k hm hlen
    simp only
    unfold native.MAX_NAME_DIGITS
    step as ⟨mx, hmx⟩
    split
    · simp
    · rename_i hlt
      have hlt' : digits.val.length < Usize.max - 8 := by
        simp only [alloc.vec.Vec.len, not_le] at hlt; scalar_tac
      have hk : (num.Integer.ofInt 10).toInt = 10 := num.Integer.toInt_ofInt 10
      rw [hten, num.Integer.euclidean_qr_spec m _ (by rw [hk]; decide), hk, hm]
      have hed : (k : Int).ediv 10 = (k : Int) / 10 := rfl
      have hem : (k : Int).emod 10 = (k : Int) % 10 := rfl
      simp only [Std.bind_ok, uncurry_apply_pair, hed, hem]
      obtain ⟨u, hu, huv⟩ := num.Integer.to_u32_spec (num.Integer.ofInt ((k : Int) % 10))
      rw [num.Integer.toInt_ofInt, if_pos (by omega)] at huv
      rw [hu]
      simp only [Std.bind_ok]
      have hu10 : u.val = k % 10 := by omega
      step as ⟨i3, hi3⟩
      step as ⟨d1, hd1⟩
      obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec (num.Integer.ofInt ((k : Int) / 10))
      rw [num.Integer.toInt_ofInt] at hsv
      rw [hsg]
      simp only [Std.bind_ok]
      have hcons : d1.val.map (fun c => c.val) =
          digits.val.map (fun c => c.val) ++ [48 + k % 10] := by
        rw [hd1]; simp; omega
      split
      · rename_i hz
        have hq : k / 10 = 0 := by
          have : sg.val = 0 := by scalar_tac
          rw [hsv] at this
          have := Int.sign_eq_zero_iff_zero.mp this
          omega
        simp only [WP.dspec_ok]
        refine ⟨?_, by simp only [hd1, List.length_append, List.length_singleton]; omega⟩
        rw [hcons, digitsRev_eq k, if_pos hq] <;> simp
      · rename_i hz
        have hq : k / 10 ≠ 0 := by
          intro h0
          apply hz
          have : (k : Int) / 10 = 0 := by omega
          rw [this] at hsv
          have h0' : sg.val = 0 := by rw [hsv]; rfl
          exact IScalar.eq_of_val_eq (by rw [h0']; rfl)
        apply WP.dspec_mono (ih d1 _ (k / 10) (by rw [num.Integer.toInt_ofInt]; omega)
          (by simp only [hd1, List.length_append, List.length_singleton]; omega))
        intro r hr
        cases r with
        | Ok ds =>
          obtain ⟨h1, h2⟩ := hr
          refine ⟨?_, h2⟩
          rw [h1, hcons, digitsRev_eq k, if_neg hq]; simp
        | Err _ => trivial

/-- The copy back to front: the first `i` digits pushed, the last first. -/
theorem constant_name_loop_spec (digits : alloc.vec.Vec Std.U32) :
    ∀ (codes : alloc.vec.Vec Std.U32) (i : Std.Usize), i.val ≤ digits.val.length →
      codes.val.length + i.val ≤ Usize.max →
      native.constant_name_loop digits codes i ⦃ r =>
        r.val.map (fun c => c.val) =
          codes.val.map (fun c => c.val) ++ ((digits.val.take i.val).reverse).map (fun c => c.val) ⦄div := by
  apply native.constant_name_loop.fixpoint_induct digits
    (motive := fun loop => ∀ (codes : alloc.vec.Vec Std.U32) (i : Std.Usize),
      i.val ≤ digits.val.length → codes.val.length + i.val ≤ Usize.max →
      loop codes i ⦃ r =>
        r.val.map (fun c => c.val) =
          codes.val.map (fun c => c.val) ++ ((digits.val.take i.val).reverse).map (fun c => c.val) ⦄div)
  · prove_adm
  · intro loop ih codes i hi hlen
    simp only
    split
    · rename_i hpos
      have hpos' : 0 < i.val := by scalar_tac
      step as ⟨i1, hi1⟩
      step as ⟨d, hd⟩
      step as ⟨codes1, hc1⟩
      apply WP.dspec_mono (ih codes1 i1 (by scalar_tac)
        (by simp only [hc1, List.length_append, List.length_singleton]; scalar_tac))
      intro r hr
      have hi' : i.val = i1.val + 1 := by scalar_tac
      have hb : i1.val < digits.val.length := by omega
      have htake : digits.val.take i.val = digits.val.take i1.val ++ [digits.val[i1.val]] := by
        rw [hi']; exact List.take_succ_eq_append_getElem hb
      rw [hr, hc1, htake]
      simp [hd]
      rw [List.take_succ_eq_append_getElem (by simpa using hb)]
      simp
    · rename_i hz
      have : i.val = 0 := by scalar_tac
      simp [this]

/-- The name of the `k`-th constant, `k ≥ 0`: the prefix, then the digits. -/
theorem constant_name_spec (uninterpreted : Bool) (n : num.Integer) (k : Nat) (hn : n.toInt = k) :
    native.constant_name uninterpreted n ⦃ r =>
      match r with
      | core.result.Result.Ok es => es.val.map (fun c => c.val) =
          [64, if uninterpreted then 117 else 99, 46] ++ (digitsRev k).reverse
      | core.result.Result.Err _ => True ⦄div := by
  unfold native.constant_name
  obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec n
  have hnn : ¬ sg < 0#i32 := by
    intro hlt
    have : sg.val < 0 := by scalar_tac
    rw [hsv, hn] at this
    rcases int_sign_cases (k : Int) with ⟨h1, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · rw [h] at this; omega
    · rw [h] at this; omega
  have hkind : (if uninterpreted then ok 117#u32 else ok 99#u32 : Result Std.U32) =
      ok (if uninterpreted then 117#u32 else 99#u32) := by split <;> rfl
  rw [hkind, hsg]
  simp only [Std.bind_ok, hnn, ite_false, num.Integer.clone_spec]
  unfold native.decimal_digits
  rw [num.Integer.from_u32_spec, num.Integer.clone_spec]
  simp only [Std.bind_ok]
  apply WP.dspec_bind (decimal_digits_loop_spec _ (by simp) _ n k hn (by simp))
  intro r hr
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok val =>
    obtain ⟨hval, hvlen⟩ := hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    step as ⟨c0, hc0⟩
    step as ⟨c1, hc1⟩
    step as ⟨c2, hc2⟩
    have hc2v : c2.val.map (fun c => c.val) = [64, if uninterpreted then 117 else 99, 46] := by
      rw [hc2, hc1, hc0]; split <;> simp
    have hc2l : c2.val.length = 3 := by rw [hc2, hc1, hc0]; simp
    apply WP.dspec_bind (constant_name_loop_spec val c2 _ (by simp [alloc.vec.Vec.len])
      (by simp only [alloc.vec.Vec.len, hc2l]; scalar_tac))
    intro codes4 h4
    simp only [eostring.EoString.from_code_points, Std.bind_ok, WP.dspec_ok]
    rw [h4, hc2v]
    simp [alloc.vec.Vec.len, hval]

/-! ## The native operation -/

/-- `uconst_id` gives a handle of logos's name of the constant. -/
theorem Store.native_spec_uconst_id (s : Store) (args : Slice Term) {a : Term} {x : Nat}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.UconstId args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.native_uconst_id x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_const_id
  simp only [Store.raw_int_rep_nat ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec (num.Integer.ofInt x)
  rw [num.Integer.toInt_ofInt] at hsv
  rw [hsg]
  have hnn : ¬ sg < 0#i32 := by
    intro hlt
    have : sg.val < 0 := by scalar_tac
    rw [hsv] at this
    rcases int_sign_cases (x : Int) with ⟨h1, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · rw [h] at this; omega
    · rw [h] at this; omega
  simp only [hnn, ite_false, Std.bind_ok]
  have heq : native.NativeOp.Insts.CoreCmpPartialEqNativeOp.eq native.NativeOp.UconstId
      native.NativeOp.UconstId = ok true := by
    simp [native.NativeOp.Insts.CoreCmpPartialEqNativeOp.eq]
  rw [heq]
  simp only [Std.bind_ok]
  apply WP.dspec_bind (constant_name_spec true (num.Integer.ofInt x) x (num.Integer.toInt_ofInt _))
  intro r hr
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok es =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    apply Store.raw_str_vec_spec s es (Smtm.native_uconst_id x) _ hinv h64
    rw [hr, native_uconst_id_codes]
    rfl

end pathos_compiled_checker
