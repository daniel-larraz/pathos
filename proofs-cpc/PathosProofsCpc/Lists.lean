module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Runtime.Lists

/-!
# CPC's list builtins (CPC only)

The list builtins that CpcMini's logos does not define, on the model of
`eo::cons` (PathosProofs/Runtime/Lists.lean): the runtime takes a list of
`f` apart (`list_parts`) and builds one (`list_build`); logos's function is
stated on the list given by its end (`eoList`).

`NilApply xf`: an application of two arguments is no nil of `xf`, which
logos decides `false`. It holds of most operators, but not of every one:
CPC's nil test of `@@TypedList_cons` is stuck, not `false`, on what is not
its nil, so logos's `eo::list_singleton_elim` of such a list of two or more
elements is stuck where the runtime (as Ethos) gives the list.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- An application of two arguments is no nil of `xf`, by logos's test. -/
def NilApply (xf : Eo.Term) : Prop :=
  ∀ g c d, Eo.__eo_is_list_nil xf (Eo.Term.Apply (Eo.Term.Apply g c) d) = Eo.Term.Boolean false

/-- `NilApply` of an operator constant: logos's test, by evaluation. -/
macro "nil_apply_tac" : tactic =>
  `(tactic| first
    | (intro _ _ _; rfl)
    | (intro g c d; simp [Eo.__eo_is_list_nil, eo_list_nil]))

theorem Store.builtin_spec_list_singleton_elim (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b : Term} {xf xa : Eo.Term} (hargs : args.val = [a, b])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) (hap : NilApply xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListSingletonElim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_singleton_elim xf xa)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListSingletonElim 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold generated.part0.Store.builtin_list
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  unfold Store.check_handles
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hxf : xf = Eo.Term.Stuck
    · subst hxf
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_singleton_elim Eo.Term.Stuck xa = Eo.Term.Stuck := by
        simp [Eo.__eo_list_singleton_elim, Eo.__eo_is_list, Eo.__eo_requires,
          SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_singleton_elim xf Eo.Term.Stuck = Eo.Term.Stuck := by
        simp [Eo.__eo_list_singleton_elim, Eo.__eo_is_list, Eo.__eo_requires,
          SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    simp only [h0, Std.bind_ok]
    unfold generated.part0.Store.list_of_one
    simp only [h1, Std.bind_ok]
    step with list_parts_spec n hnil s hinv h64 hrem ha hb hleft as ⟨r, s1, hinv1, hg1, hr⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact ⟨hinv1, hg1⟩
    | Ok o =>
      cases o with
      | none =>
        obtain ⟨ys, xr, hxl, hend, hn⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Store.stuck_eq,
          WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv1, hg1, ?_⟩
        have : Eo.__eo_list_singleton_elim xf xa = Eo.Term.Stuck := by
          rw [show Eo.__eo_list_singleton_elim xf xa = Eo.__eo_requires (Eo.__eo_is_list xf xa)
            (Eo.Term.Boolean true) (Eo.__eo_list_singleton_elim_2 xa) from rfl]
          rw [hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hl : Eo.__eo_is_list xf xa = Eo.Term.Boolean true := by
          rw [hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]; simp [hn]
        have hval : Eo.__eo_list_singleton_elim xf xa = Eo.__eo_list_singleton_elim_2 xa := by
          rw [show Eo.__eo_list_singleton_elim xf xa = Eo.__eo_requires (Eo.__eo_is_list xf xa)
              (Eo.Term.Boolean true) (Eo.__eo_list_singleton_elim_2 xa) from rfl]
          simp [hl, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        rw [hval]
        have hlen' := hys.length_eq
        rcases ys with _ | ⟨y, _ | ⟨y2, ys⟩⟩
        · -- no element: the list is its nil
          have hz : tail.val.length = 0 := by simpa using hlen'
          have hi : ¬ (alloc.vec.Vec.len tail = 1#usize) := by
            intro h; have := congrArg UScalar.val h; simp [alloc.vec.Vec.len] at this; omega
          show (if alloc.vec.Vec.len tail = 1#usize then _ else _) ⦃ r s' => _ ⦄div
          simp only [hi, ite_false, WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv1, hg1, ?_⟩
          have hna := is_list_nil_not_apply hn
          have : Eo.__eo_list_singleton_elim_2 xa = xa := by
            rw [hxl]; simp only [eoList]
            unfold Eo.__eo_list_singleton_elim_2; split <;> simp_all
          rw [this]; exact Represents.grows hb hg1
        · -- one element: it
          have hi : alloc.vec.Vec.len tail = 1#usize := by
            apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len]; simpa using hlen'
          show (if alloc.vec.Vec.len tail = 1#usize then _ else _) ⦃ r s' => _ ⦄div
          simp only [hi, ite_true]
          generalize hvl : tail.val = l at hys
          cases hys with
          | cons hy hrest' =>
            cases hrest'
            rename_i t0
            have hidx : alloc.vec.Vec.index_usize tail 0#usize = ok t0 := by
              simp [alloc.vec.Vec.index_usize, hvl]
            simp only [hidx, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv1, hg1, ?_⟩
            have : Eo.__eo_list_singleton_elim_2 xa = y := by
              rw [hxl]; simp [eoList, Eo.__eo_list_singleton_elim_2, hn, Eo.__eo_ite,
                SmtEval.native_ite, Eo.native_teq]
            rw [this]; exact hy
        · -- two or more: the list itself
          have hi : ¬ (alloc.vec.Vec.len tail = 1#usize) := by
            intro h
            have h1 : tail.val.length = 1 := by
              have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len] using this
            simp at hlen'; omega
          show (if alloc.vec.Vec.len tail = 1#usize then _ else _) ⦃ r s' => _ ⦄div
          simp only [hi, ite_false, WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv1, hg1, ?_⟩
          have : Eo.__eo_list_singleton_elim_2 xa = xa := by
            have h2 := hap xf y2 (eoList xf xr ys)
            rw [hxl]; simp [eoList, Eo.__eo_list_singleton_elim_2, h2, Eo.__eo_ite,
              SmtEval.native_ite, Eo.native_teq]
          rw [this]; exact Represents.grows hb hg1

end pathos_compiled_checker
