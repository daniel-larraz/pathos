module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import PathosProofs.Runtime.Builtins
public import PathosProofs.Runtime.CompareTerm

/-!
# `eo::cmp` (CPC only)

The builtin `eo::cmp`: stuck when an argument is, else the Boolean of
whether the first term is below the second in logos's order (`__eo_cmp`,
`native_tcmp`). The runtime orders the two terms with `Store::compare`,
which gives logos's `termCmp` of the terms (`compare_rep_spec`,
`Runtime/CompareTerm.lean`). CPC only, as CpcMini's logos has no
`__eo_cmp`.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

theorem Store.builtin_spec_cmp (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Compare args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_cmp x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Compare 2#usize = ok true := by
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
      have : Eo.__eo_cmp Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_cmp]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_cmp x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_cmp; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false, h0, h1,
      Std.bind_ok]
    apply WP.dspec_bind (compare_rep_spec s hinv h64 a b ha hb)
    intro r hr
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact ⟨hinv, Store.Grows.refl s⟩
    | Ok o =>
      obtain rfl := hr o rfl
      have he : Eo.__eo_cmp x y = Eo.Term.Boolean (Eo.native_tcmp x y) := by
        unfold Eo.__eo_cmp; split <;> simp_all
      rw [he]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Store.boolean]
      have hl : native.is_less (Eo.termCmp x y) = ok (Eo.native_tcmp x y) := by
        unfold native.is_less Eo.native_tcmp; split <;> simp_all
      rw [hl, Std.bind_ok]
      exact Store.literal_boolean_spec s _ hinv h64

end pathos_compiled_checker
