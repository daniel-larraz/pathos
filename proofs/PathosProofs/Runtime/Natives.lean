module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtTranslate
import all CpcMini.SmtTranslate
public import PathosProofs.Util
public import PathosProofs.Eunoia.Natives
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops

/-!
# The runtime's native operations

What `native_op` gives for each operation that generated code calls, in
the form the generated proofs use (`Store.native_spec_<the operation>`):
on handles of the arguments, a handle of logos's native of their values.

The equalities (`teq`, `Teq`, `streq`) compare handles; that this is
comparing values is `Represents.eq_iff` (a value has one handle). `and`
and `or` read the native Booleans of their handles.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `native_op` on two arguments: the arity test passes and the first
handle is read. -/
theorem native_op_two (s : Store) (op : native.NativeOp) (args : Slice Term) {a b : Term}
    (hargs : args.val = [a, b]) (hop : native.NativeOp.arity op = ok 2#usize)
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
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by
    simp [Slice.index_usize, hargs]
  rw [hk, hlen, hop, h0]
  simp

theorem slice_index_one {args : Slice Term} {a b : Term} (hargs : args.val = [a, b]) :
    Slice.index_usize args 1#usize = ok b := by
  simp [Slice.index_usize, hargs]

/-- Two handles compared: whether their values are equal. -/
theorem Store.native_teq_gen {α : Type} [Embedded α] [DecidableEq α] (s : Store) (args : Slice Term) {a b : Term}
    {x y : α} (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Teq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (decide (x = y))
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok, Term.Insts.CoreCmpPartialEqTerm.eq]
  have hd : decide (a = b) = decide (x = y) := by
    simp [Represents.eq_iff hinv ha hb]
  rw [hd]
  exact Store.native_bool_spec s _ hinv h64

/-- `teq` on terms. -/
theorem Store.native_spec_teq (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Teq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.native_teq x y)
      | core.result.Result.Err _ => True ⦄div :=
  Store.native_teq_gen s args hargs ha hb hinv h64

/-- `Teq` on SMT types. -/
theorem Store.native_spec_Teq (s : Store) (args : Slice Term) {a b : Term} {x y : Smtm.SmtType}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Teq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.native_Teq x y)
      | core.result.Result.Err _ => True ⦄div :=
  Store.native_teq_gen s args hargs ha hb hinv h64

/-- `streq`: compares the handles of the two strings (after reading both). -/
theorem Store.native_spec_streq (s : Store) (args : Slice Term) {a b : Term}
    {x y : Eunoia.native_String}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Streq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_streq x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  unfold native.Store.native_streq
  rw [Store.view_eq, Store.view_eq]
  simp only [Represents.lt ha, Represents.lt hb, ite_true, Std.bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, Term.Insts.CoreCmpPartialEqTerm.eq]
  have hd : decide (a = b) = Eunoia.native_streq x y := by
    simp [Eunoia.native_streq, Represents.eq_iff hinv ha hb]
  rw [hd]
  exact Store.native_bool_spec s _ hinv h64

/-- `and` and `or` read the native Booleans of their handles. -/
theorem Store.native_connective_spec (s : Store) (op : native.NativeOp) {a b : Term} {x y : Bool}
    (ha : Represents.rep s a x) (hb : Represents.rep s b y) :
    native.Store.native_connective s op a b =
      (match op with
        | native.NativeOp.And => native.Store.native_bool s (x && y)
        | native.NativeOp.Or => native.Store.native_bool s (x || y)
        | _ => native.Store.native_connective s op a b) := by
  rcases Store.boolean_value_native ha with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
  rcases Store.boolean_value_native hb with ⟨rfl, hy⟩ | ⟨rfl, hy⟩ <;>
  cases op <;> first
    | rfl
    | simp [native.Store.native_connective, hx, hy, core.result.Result.Insts.CoreOpsTry.branch]

theorem Store.native_spec_and (s : Store) (args : Slice Term) {a b : Term} {x y : Bool}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.And args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_and x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  rw [Store.native_connective_spec s _ ha hb]
  exact Store.native_bool_spec s _ hinv h64

theorem Store.native_spec_or (s : Store) (args : Slice Term) {a b : Term} {x y : Bool}
    (hargs : args.val = [a, b]) (ha : Represents.rep s a x) (hb : Represents.rep s b y)
    (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_op s native.NativeOp.Or args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eunoia.native_or x y)
      | core.result.Result.Err _ => True ⦄div := by
  rw [native_op_two s _ args hargs rfl _ (by rw [native.Store.native_op])]
  simp only [slice_index_one hargs, Std.bind_ok]
  rw [Store.native_connective_spec s _ ha hb]
  exact Store.native_bool_spec s _ hinv h64

/-! ## The builtin `eo::eq`

`builtin_core` with `Eq`: the stuck term if either argument is stuck, else
the Boolean of the comparison of the two handles, which is the comparison
of the two terms (`Represents.eq_iff`). -/

/-- `stuck_or_foreign` on a handle of a term: whether it is the stuck term. -/
theorem Store.stuck_or_foreign_rep {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    Store.stuck_or_foreign s t = ok (decide (x = Eo.Term.Stuck)) := by
  unfold Store.stuck_or_foreign
  rw [Store.view_eq]
  simp only [h.lt, ite_true, Std.bind_ok]
  have hs := h.stuck_iff
  unfold Store.data at hs
  cases hd : s.nodes.val[t.val]! <;> simp_all [TermData.isStuck]

/-- `any_stuck` on the handles of two terms. -/
theorem Store.any_stuck_two {s : Store} {args : Slice Term} {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y) :
    Store.any_stuck s args ⦃ r => r = (decide (x = Eo.Term.Stuck) || decide (y = Eo.Term.Stuck)) ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  unfold Store.any_stuck
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt0 : (0#usize : Std.Usize) < 2#usize := by scalar_tac
  simp only [hlt0, ite_true]
  have hite : ∀ c : Bool, (if c = true then (ok true : Result Bool) else ok false) = ok c := by
    intro c; cases c <;> rfl
  have hite' : ∀ c d : Bool, (if c = true then (ok true : Result Bool) else ok d) = ok (c || d) := by
    intro c d; cases c <;> rfl
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  simp only [h0, Store.stuck_or_foreign_rep ha, Std.bind_ok, hite]
  step as ⟨i1, hi1⟩
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt1 : i1 < 2#usize := by scalar_tac
  have h1 : Slice.index_usize args i1 = ok b := by
    simp [Slice.index_usize, hargs, show i1.val = 1 by scalar_tac]
  simp only [hlt1, ite_true, h1, Store.stuck_or_foreign_rep hb, Std.bind_ok, hite']
  step as ⟨i2, hi2⟩
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt2 : ¬ (i2 < 2#usize) := by scalar_tac
  simp only [hlt2, ite_false]
  simp [Bool.or_comm]

theorem Store.builtin_spec_eq (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Eq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_eq x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Eq 2#usize = ok true := by
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
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_eq Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_eq]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_eq x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_eq; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false, h1,
      Std.bind_ok, Term.Insts.CoreCmpPartialEqTerm.eq, Store.boolean]
    have hd : decide (a = b) = decide (y = x) := by
      simp [Represents.eq_iff hinv ha hb, eq_comm]
    rw [hd, eo_eq_of_ne x y hx hy]
    exact Store.literal_boolean_spec s _ hinv h64

/-- `eo::is_ok` on a handle of a term: whether it is not stuck. -/
theorem Store.builtin_spec_is_ok (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsOk args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_ok x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsOk 1#usize = ok true := by
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0,
      Store.Rep.is_stuck ha, Store.boolean]
    have hv : Eo.__eo_is_ok x = Eo.Term.Boolean (!decide (x = Eo.Term.Stuck)) := by
      simp [Eo.__eo_is_ok, Eo.native_teq, SmtEval.native_not]
    rw [hv]
    exact Store.literal_boolean_spec s _ hinv h64

end pathos_compiled_checker
