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

/-! ## `eo::list_concat` -/

/-- The operator has one nil: two terms that logos's test takes for nils of
`xf` are one. Where it fails (`str.++`, the bit-vector operators, `+`,
`*`, `@@TypedList.cons`), logos concatenates two lists that end in
different nils, which Ethos and the runtime do not (docs/proofs.md,
"`eo::list_concat` and the nils of an operator"). -/
def UniqueNil (xf : Eo.Term) : Prop :=
  ∀ a b, Eo.__eo_is_list_nil xf a = Eo.Term.Boolean true →
    Eo.__eo_is_list_nil xf b = Eo.Term.Boolean true → a = b

/-- `UniqueNil` of an operator constant whose nil test has one closed
pattern: logos's test, by evaluation. -/
macro "unique_nil_tac" : tactic =>
  `(tactic| (intro a b ha hb
             revert ha hb
             unfold Eo.__eo_is_list_nil
             split <;> split <;> simp_all))

theorem eoList_ne_stuck {xf e : Eo.Term} (he : e ≠ Eo.Term.Stuck) :
    ∀ xs, eoList xf e xs ≠ Eo.Term.Stuck
  | [] => he
  | _ :: _ => by simp [eoList]

theorem eoList_append (xf e : Eo.Term) (xs ys : List Eo.Term) :
    eoList xf e (xs ++ ys) = eoList xf (eoList xf e ys) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [eoList, ih]

/-- logos's `list_concat_rec` puts the elements of the first list before
the second, whole. -/
theorem concat_rec_eoList {xf xr b : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck)
    (hb : b ≠ Eo.Term.Stuck) :
    ∀ xs, Eo.__eo_list_concat_rec (eoList xf xr xs) b = eoList xf b xs := by
  intro xs
  induction xs with
  | nil =>
    simp only [eoList]
    unfold Eo.__eo_list_concat_rec
    split <;> simp_all
  | cons x xs ih =>
    simp only [eoList]
    rw [Eo.__eo_list_concat_rec.eq_def]
    simp [ih, Eo.__eo_mk_apply, hb, eoList_ne_stuck hb]

/-- logos's `eo::list_concat` on two lists of `f`, given by their ends. -/
theorem eo_list_concat_eoList {xf xr yr : Eo.Term} (xs ys : List Eo.Term)
    (hnf : xf ≠ Eo.Term.Stuck)
    (hnx : eoList xf xr xs ≠ Eo.Term.Stuck) (hny : eoList xf yr ys ≠ Eo.Term.Stuck)
    (hendx : ∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b)
    (hendy : ∀ a b, yr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) :
    Eo.__eo_list_concat xf (eoList xf xr xs) (eoList xf yr ys) =
      if Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true ∧
          Eo.__eo_is_list_nil xf yr = Eo.Term.Boolean true then
        eoList xf (eoList xf yr ys) xs
      else Eo.Term.Stuck := by
  show Eo.__eo_requires (Eo.__eo_is_list xf (eoList xf xr xs)) (Eo.Term.Boolean true)
    (Eo.__eo_requires (Eo.__eo_is_list xf (eoList xf yr ys)) (Eo.Term.Boolean true)
      (Eo.__eo_list_concat_rec (eoList xf xr xs) (eoList xf yr ys))) = _
  rw [is_list_eoList xs hnf hnx hendx, is_list_eoList ys hnf hny hendy]
  by_cases hx : Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true
  · by_cases hy : Eo.__eo_is_list_nil xf yr = Eo.Term.Boolean true
    · have hxr : xr ≠ Eo.Term.Stuck := by
        intro h; subst h; revert hx; unfold Eo.__eo_is_list_nil; split <;> simp_all
      rw [concat_rec_eoList (is_list_nil_not_apply hx) hxr hny xs]
      simp [hx, hy, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not,
        eoList_ne_stuck hny]
    · simp [hx, hy, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
  · simp [hx, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]

/-- `list_pair`: the elements of two lists of `f` that end in one nil, and
that nil; where they do not, logos's `eo::list_concat` is stuck (given
that `f` has one nil). -/
theorem list_pair_spec (n : Nat) (hnil : IsListNilSpec n) (s : Store) (hinv : s.Inv)
    (h64 : Platform64) (hrem : s.remaining ≤ n) {fh xh yh : Term} {xf xa xb : Eo.Term}
    (hf : s.Rep fh xf) (hx : s.Rep xh xa) (hy : s.Rep yh xb)
    (hxf : xf ≠ Eo.Term.Stuck) (hxa : xa ≠ Eo.Term.Stuck) (hxb : xb ≠ Eo.Term.Stuck)
    (hleft : NotLeftNested xf) (huniq : UniqueNil xf) :
    generated.part0.Store.list_pair s fh xh yh ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (xsh, ysh, nilh)) =>
        ∃ xs ys xr, List.Forall₂ s'.Rep xsh.val xs ∧ List.Forall₂ s'.Rep ysh.val ys ∧
          s'.Rep nilh xr ∧ xa = eoList xf xr xs ∧ xb = eoList xf xr ys ∧
          (∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) ∧
          Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true ∧
          xsh.val.length ≤ 2 ^ 32 ∧ ysh.val.length ≤ 2 ^ 32
      | core.result.Result.Ok none => Eo.__eo_list_concat xf xa xb = Eo.Term.Stuck
      | core.result.Result.Err _ => True ⦄div := by
  have hcat : ∀ y z, Eo.__eo_list_concat xf y z = Eo.__eo_requires (Eo.__eo_is_list xf y)
      (Eo.Term.Boolean true) (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true)
        (Eo.__eo_list_concat_rec y z)) := fun _ _ => rfl
  unfold generated.part0.Store.list_pair
  step with list_parts_spec n hnil s hinv h64 hrem hf hx hleft as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv1, hg1⟩
  | Ok o =>
    cases o with
    | none =>
      obtain ⟨xs, xr, hxl, hend, hn⟩ := hr
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv1, hg1, ?_⟩
      rw [hcat, hxl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hend]
      simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
    | some p =>
      obtain ⟨xsh, xrh⟩ := p
      obtain ⟨xs, xr, hxs, hxrh, hxl, hendx, hnx, hszx⟩ := hr
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      step with list_parts_spec n hnil s1 hinv1 h64 (hg1.rem hrem) (Represents.grows hf hg1)
        (Represents.grows hy hg1) hleft as ⟨r2, s2, hinv2, hg2, hr2⟩
      cases r2 with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv2, hg1.trans hg2⟩
      | Ok o2 =>
        have hlx : Eo.__eo_is_list xf xa = Eo.Term.Boolean true := by
          rw [hxl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hendx]; simp [hnx]
        cases o2 with
        | none =>
          obtain ⟨ys, yr, hyl, hendy, hny⟩ := hr2
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, WP.dspec_ok,
            WP.uncurry'_pair]
          refine ⟨hinv2, hg1.trans hg2, ?_⟩
          rw [hcat, hlx, hyl, is_list_eoList ys hxf (by rw [← hyl]; exact hxb) hendy]
          simp [hny, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        | some p2 =>
          obtain ⟨ysh, yrh⟩ := p2
          obtain ⟨ys, yr, hys, hyrh, hyl, hendy, hny, hszy⟩ := hr2
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, term_ne]
          have hxrh2 := Represents.grows hxrh hg2
          have hmax := hinv.table.hmax
          have hmax1 := hinv1.table.hmax
          have hn0 : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
          have hn1 : s1.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
          by_cases hq : yrh = xrh
          · have hxy : yr = xr := (Represents.eq_iff hinv2 hyrh hxrh2).mp hq
            subst hxy
            show (if (!decide (yrh = xrh)) = true then ok (core.result.Result.Ok none, s2)
              else ok (core.result.Result.Ok (some (xsh, ysh, xrh)), s2)) ⦃ r s' => _ ⦄div
            simp only [hq, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
              WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv2, hg1.trans hg2, xs, ys, yr,
              hxs.imp (fun {_ _} h => Represents.grows h hg2), hys, hxrh2, hxl, hyl, hendx, hnx,
              ?_, ?_⟩
            · simp only [alloc.vec.Vec.length] at hszx; omega
            · simp only [alloc.vec.Vec.length] at hszy; omega
          · exfalso
            have hne : yr ≠ xr := fun h => hq ((Represents.eq_iff hinv2 hyrh hxrh2).mpr h)
            exact hne (huniq _ _ hny hnx)

/-- `eo::list_concat` on handles of an operator with one nil and two terms:
logos's `__eo_list_concat`. -/
theorem Store.builtin_spec_list_concat (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xb : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xb)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n)
    (hleft : NotLeftNested xf) (huniq : UniqueNil xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListConcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_concat xf xa xb)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListConcat 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hcat : ∀ y z, Eo.__eo_list_concat xf y z = Eo.__eo_requires (Eo.__eo_is_list xf y)
      (Eo.Term.Boolean true) (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true)
        (Eo.__eo_list_concat_rec y z)) := fun _ _ => rfl
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
    step with Store.any_stuck_three hargs ha hb hc as ⟨b1, hb1⟩
    subst hb1
    by_cases hxf : xf = Eo.Term.Stuck
    · subst hxf
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_concat Eo.Term.Stuck xa xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_concat xf Eo.Term.Stuck xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxb : xb = Eo.Term.Stuck
    · subst hxb
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_concat xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hcat]
        have h2 : Eo.__eo_is_list xf Eo.Term.Stuck = Eo.Term.Stuck := by
          unfold Eo.__eo_is_list; split <;> simp_all
        simp [h2, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hxb, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
    simp only [h0, h1, h2, Std.bind_ok]
    unfold generated.part0.Store.list_concat
    have hva : TermValid xa := Store.Rep.valid' hinv hb
    have hvb : TermValid xb := Store.Rep.valid' hinv hc
    step with list_pair_spec n hnil s hinv h64 hrem ha hb hc hxf hxa hxb hleft huniq
      as ⟨r, s2, hinv2, hg2, hr⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact ⟨hinv2, hg2⟩
    | Ok o =>
      cases o with
      | none =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Store.stuck_eq,
          WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv2, hg2, ?_⟩
        rw [hr]; exact hinv2.rep_stuck
      | some p =>
        obtain ⟨xsh, ysh, nilh⟩ := p
        obtain ⟨xs, ys, xr, hxs, hys, hnilh, hxl, hyl, hend, hn, hlx', hly'⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have haf := Represents.grows ha hg2
        rw [is_left_assoc_false s2 haf hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
          Bool.false_eq_true, ite_false]
        have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        step as ⟨i2, hi2⟩
        have hwc : (alloc.vec.Vec.with_capacity Term i2).val = [] := by
          simp [alloc.vec.Vec.with_capacity]
        unfold append_terms
        step with append_terms_loop_spec xsh.deref (alloc.vec.Vec.with_capacity Term i2)
          0#usize (by simp) (by rw [hwc]; simp [alloc.vec.Vec.deref, Slice.length]; omega)
          as ⟨both1, hb1⟩
        rw [hwc] at hb1
        step with append_terms_loop_spec ysh.deref both1 0#usize (by simp)
          (by rw [hb1]; simp [alloc.vec.Vec.deref, Slice.length]; omega) as ⟨both2, hb2⟩
        simp only [List.nil_append, List.drop_zero] at hb1 hb2
        have hb2' : both2.val = xsh.val ++ ysh.val := by
          rw [hb2, hb1]; simp [alloc.vec.Vec.deref]
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hall : List.Forall₂ s2.Rep (alloc.vec.Vec.deref both2).val (xs ++ ys) := by
          have : (alloc.vec.Vec.deref both2).val = both2.val := by
            simp [alloc.vec.Vec.deref]
          rw [this, hb2']
          exact List.rel_append hxs hys
        have hnys : ∀ y ∈ xs ++ ys, y ≠ Eo.Term.Stuck := by
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact eoList_valid_elems xs (hxl ▸ hva) y hy
          · exact eoList_valid_elems ys (hyl ▸ hvb) y hy
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s2 haf hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref both2)).val = (xs ++ ys).length := by
          have := hall.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s2 h64 (alloc.vec.Vec.deref both2)
          (xs ++ ys) hall hxf hnys hxr s2 nilh (Slice.len (alloc.vec.Vec.deref both2)) hinv2
          (Store.Grows.refl s2) haf (by omega)
          (by rw [hlenE, List.drop_length]; exact hnilh))
        rintro ⟨r3, s3⟩ ⟨hinv3, hg3, hr3⟩
        refine ⟨hinv3, hg2.trans hg3, ?_⟩
        cases r3 with
        | Err e => trivial
        | Ok t =>
          simp only at hr3 ⊢
          have hval : Eo.__eo_list_concat xf xa xb = eoList xf (eoList xf xr ys) xs := by
            rw [hxl, hyl, eo_list_concat_eoList xs ys hxf (by rw [← hxl]; exact hxa)
              (by rw [← hyl]; exact hxb) hend hend]
            simp [hn]
          rw [hval, ← eoList_append]; exact hr3

end pathos_compiled_checker
