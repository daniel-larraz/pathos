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

/-!
# The runtime's `not` and its string operations

What `native_op` gives for `not`, `string_valid` and `string_prefix_eq`:
on handles of the arguments, a handle of logos's native. A native string
is stored as its code points (`Tree.strOf`: each below 2^32, as the
embedding's `okStr` says), and the two string operations are loops over
them, proved by induction over the loop.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `native_op` on `n` arguments: the arity test passes and the first
handle is read. -/
theorem native_op_n (s : Store) (op : native.NativeOp) (args : Slice Term) {a : Term}
    (n : Std.Usize) (hlen : Slice.len args = n) (hop : native.NativeOp.arity op = ok n)
    (h0 : Slice.index_usize args 0#usize = ok a)
    (k : Term → Result ((core.result.Result Term CheckError) × Store))
    (hk : native.Store.native_op s op args =
      (do
        let i := Slice.len args
        let i1 ← native.NativeOp.arity op
        if i != i1 then ok (core.result.Result.Err CheckError.InvalidNative, s)
        else
          let x ← Slice.index_usize args 0#usize
          k x)) :
    native.Store.native_op s op args = k a := by
  rw [hk, hlen, hop, h0]
  simp

/-! ## `not` -/

theorem Store.native_spec_not (s : Store) (args : Slice Term) {a : Term} {x : Bool}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Not args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_not x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_not native.Store.native_bool_value
  rcases Store.boolean_value_native ha with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;>
  · simp only [hb, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    exact Store.native_bool_spec s _ hinv h64

/-! ## Reading a native string -/

theorem Store.native_string_rep {s : Store} {t : Term} {x : List Nat}
    (h : Represents.rep s t x) :
    native.Store.native_string s t = ok (core.result.Result.Ok (Tree.strOf x)) := by
  obtain ⟨hh, _⟩ := h
  unfold native.Store.native_string
  rw [Store.view_eq]
  simp only [hh.lt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  simp only [Tree.embedded_enc_Str, Tree.encStr] at hh
  cases hh with
  | native _ _ _ hd => rw [hd]

/-- The code points of a string the store can hold. -/
theorem Tree.strOf_val (x : List Nat) (h : Tree.okStr x) :
    (Tree.strOf x).val = x.map Tree.u32Wrap := by
  unfold Tree.strOf
  rw [dif_pos h.1, alloc.vec.Vec.from_val]

theorem Tree.u32Wrap_val_of (x : List Nat) (h : Tree.okStr x) :
    (x.map Tree.u32Wrap).map (fun c => c.val) = x := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id x]
  exact List.map_congr_left (fun c hc => Tree.u32Wrap_val c (h.2 c hc))

theorem max_code_point_eq : MAX_CODE_POINT = 196607#u32 := by
  unfold MAX_CODE_POINT; rfl

/-- The loop of `string_valid`: whether the code points from `i` on are at
most `MAX_CODE_POINT`, and `valid`. -/
theorem string_valid_loop_spec (codes : Slice Std.U32) (valid : Bool) (i : Std.Usize) :
    native.Store.native_string_valid_loop codes valid i ⦃ r =>
      r = (valid && (codes.val.drop i.val).all (fun c => decide (c.val ≤ 196607))) ⦄div := by
  revert valid i
  apply native.Store.native_string_valid_loop.fixpoint_induct codes
    (motive := fun f => ∀ (valid : Bool) (i : Std.Usize), f valid i ⦃ r =>
      r = (valid && (codes.val.drop i.val).all (fun c => decide (c.val ≤ 196607))) ⦄div)
  · prove_adm
  · intro loop ih valid i
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < codes.length := by scalar_tac
      step as ⟨c, hc⟩
      have hdrop : codes.val.drop i.val = c :: codes.val.drop (i.val + 1) := by
        rw [hc]; exact List.drop_eq_getElem_cons hlt'
      rw [hdrop, max_code_point_eq]
      split
      · rename_i hge
        step as ⟨i3, hi3⟩
        apply WP.dspec_mono (ih false i3)
        intro r hr
        have hc' : ¬ c.val ≤ 196607 := by scalar_tac
        simp [hr, hc']
      · rename_i hge
        step as ⟨i3, hi3⟩
        apply WP.dspec_mono (ih valid i3)
        intro r hr
        have hc' : c.val ≤ 196607 := by scalar_tac
        rw [hr, show i3.val = i.val + 1 by scalar_tac]
        simp [hc']
    · rename_i hge
      have : codes.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      simp [this]

theorem Store.native_spec_string_valid (s : Store) (args : Slice Term) {a : Term}
    {x : Eunoia.native_String}
    (hargs : args.val = [a]) (ha : Represents.rep s a x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.StringValid args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_string_valid x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 1#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  unfold native.Store.native_string_valid
  simp only [Store.native_string_rep ha, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    eostring.EoString.code_points]
  step with string_valid_loop_spec as ⟨v, hv⟩
  have hok : Tree.okStr x := ha.2
  have hvx : v = Eunoia.native_string_valid x := by
    rw [hv]
    simp only [Bool.true_and, List.drop_zero]
    have hval : (alloc.vec.Vec.deref (Tree.strOf x)).val = x.map Tree.u32Wrap := by
      simp [alloc.vec.Vec.deref, Tree.strOf_val x hok]
    rw [hval, List.all_map]
    unfold Eunoia.native_string_valid Eunoia.native_char_valid Eunoia.native_z_max_code_point
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, Function.comp, decide_eq_true_eq]
    constructor <;> intro h c hc <;> have := h c hc <;> rw [Tree.u32Wrap_val c (hok.2 c hc)] at * <;>
      exact_mod_cast this
  rw [hvx]
  exact Store.native_bool_spec s _ hinv h64

/-! ## `string_prefix_eq` -/

/-- logos's prefix test is `isPrefixOf`. -/
theorem string_prefix_eq_isPrefixOf (a b : List Nat) :
    Eunoia.native_string_prefix_eq a b = a.isPrefixOf b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons c cs ih =>
    cases b with
    | nil => rfl
    | cons d ds =>
      simp only [Eunoia.native_string_prefix_eq, List.isPrefixOf, ih]
      cases h : decide (c = d) <;> simp_all

/-- The code points of two strings the store can hold: one is a prefix of
the other exactly when the strings are. -/
theorem isPrefixOf_map_u32Wrap (a b : List Nat) (ha : ∀ c ∈ a, c < 2 ^ 32)
    (hb : ∀ c ∈ b, c < 2 ^ 32) :
    (a.map Tree.u32Wrap).isPrefixOf (b.map Tree.u32Wrap) = a.isPrefixOf b := by
  induction a generalizing b with
  | nil => rfl
  | cons c cs ih =>
    cases b with
    | nil => rfl
    | cons d ds =>
      have hc := ha c (by simp)
      have hd := hb d (by simp)
      have hw : (Tree.u32Wrap c == Tree.u32Wrap d) = (c == d) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        constructor
        · intro h
          have := congrArg (fun u : Std.U32 => u.val) h
          simpa [Tree.u32Wrap_val c hc, Tree.u32Wrap_val d hd] using this
        · intro h; rw [h]
      simp only [List.map_cons, List.isPrefixOf, hw]
      rw [ih ds (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx]))]

/-- The loop of `is_prefix`: from `i` on, whether the rest of `x` is a
prefix of the rest of `y`, and `prefix`. -/
theorem is_prefix_loop_spec (x y : Slice Std.U32) (hxy : x.length ≤ y.length) (p : Bool)
    (i : Std.Usize) :
    native.is_prefix_loop x y p i ⦃ r =>
      r = (p && (x.val.drop i.val).isPrefixOf (y.val.drop i.val)) ⦄div := by
  revert p i
  apply native.is_prefix_loop.fixpoint_induct x y
    (motive := fun f => ∀ (p : Bool) (i : Std.Usize), f p i ⦃ r =>
      r = (p && (x.val.drop i.val).isPrefixOf (y.val.drop i.val)) ⦄div)
  · prove_adm
  · intro loop ih p i
    simp only
    split
    · rename_i hlt
      have hx' : i.val < x.length := by scalar_tac
      have hy' : i.val < y.length := by scalar_tac
      step as ⟨c, hc⟩
      step as ⟨d, hd⟩
      have hdx : x.val.drop i.val = c :: x.val.drop (i.val + 1) := by
        rw [hc]; exact List.drop_eq_getElem_cons hx'
      have hdy : y.val.drop i.val = d :: y.val.drop (i.val + 1) := by
        rw [hd]; exact List.drop_eq_getElem_cons hy'
      rw [hdx, hdy]
      have hne : (c != d) = !(c == d) := rfl
      split
      · rename_i hcd
        step as ⟨i3, hi3⟩
        apply WP.dspec_mono (ih false i3)
        intro r hr
        have : (c == d) = false := by simpa [hne] using hcd
        simp [hr, List.isPrefixOf, this]
      · rename_i hcd
        step as ⟨i3, hi3⟩
        apply WP.dspec_mono (ih p i3)
        intro r hr
        have hcd' : c = d := by
          apply UScalar.eq_of_val_eq; simpa [hne] using hcd
        subst hcd'
        rw [hr, show i3.val = i.val + 1 by scalar_tac]
        simp [List.isPrefixOf]
    · rename_i hge
      have : x.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      simp [this, List.isPrefixOf]

theorem is_prefix_spec (x y : Slice Std.U32) :
    native.is_prefix x y ⦃ r => r = x.val.isPrefixOf y.val ⦄div := by
  unfold native.is_prefix
  dsimp only
  split
  · rename_i hgt
    simp only [WP.dspec_ok]
    have hlen : y.val.length < x.val.length := by scalar_tac
    cases h : x.val.isPrefixOf y.val
    · rfl
    · have := (List.isPrefixOf_iff_prefix.mp h).length_le
      omega
  · rename_i hle
    apply WP.dspec_mono (is_prefix_loop_spec x y (by scalar_tac) true 0#usize)
    intro r hr
    simpa using hr

theorem Store.native_spec_string_prefix_eq (s : Store) (args : Slice Term) {a b : Term}
    {x y : Eunoia.native_String}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.StringPrefixEq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_string_prefix_eq x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
  rw [native_op_n s _ args 2#usize hlen rfl h0 _ (by rw [native.Store.native_op])]
  simp only [h1, Std.bind_ok]
  unfold native.Store.native_string_prefix_eq
  rw [Store.view_eq, Store.view_eq]
  simp only [Represents.lt ha, Represents.lt hb, ite_true, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, Store.native_string_rep ha,
    Store.native_string_rep hb, eostring.EoString.code_points]
  step with is_prefix_spec as ⟨v, hv⟩
  have hx : Tree.okStr x := ha.2
  have hy : Tree.okStr y := hb.2
  have hvx : v = Eunoia.native_string_prefix_eq x y := by
    rw [hv, string_prefix_eq_isPrefixOf]
    have h1 : (alloc.vec.Vec.deref (Tree.strOf x)).val = x.map Tree.u32Wrap := by
      simp [alloc.vec.Vec.deref, Tree.strOf_val x hx]
    have h2 : (alloc.vec.Vec.deref (Tree.strOf y)).val = y.map Tree.u32Wrap := by
      simp [alloc.vec.Vec.deref, Tree.strOf_val y hy]
    rw [h1, h2, isPrefixOf_map_u32Wrap x y hx.2 hy.2]
  rw [hvx]
  exact Store.native_bool_spec s _ hinv h64

end pathos_compiled_checker
