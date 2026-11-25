module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Runtime.Lists
public import PathosProofs.Runtime.Numbers
public import PathosProofs.Runtime.Builtins
public import PathosProofsCpc.Counts

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
          xsh.val.length < 2 ^ 32 ∧ ysh.val.length < 2 ^ 32
      | core.result.Result.Ok none =>
        Eo.__eo_is_list xf xa ≠ Eo.Term.Boolean true ∨ Eo.__eo_is_list xf xb ≠ Eo.Term.Boolean true
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
      refine ⟨hinv1, hg1, Or.inl ?_⟩
      rw [hxl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hend]
      simp [hn]
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
          refine ⟨hinv2, hg1.trans hg2, Or.inr ?_⟩
          rw [hyl, is_list_eoList ys hxf (by rw [← hyl]; exact hxb) hendy]
          simp [hny]
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
            · simp only [alloc.vec.Vec.length] at hszx; scalar_tac
            · simp only [alloc.vec.Vec.length] at hszy; scalar_tac
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
        have : Eo.__eo_list_concat xf xa xb = Eo.Term.Stuck := by
          rw [hcat]
          rcases hr with h | h
          · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h]
          · by_cases h1 : Eo.__eo_is_list xf xa = Eo.Term.Boolean true
            · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h, h1]
            · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h1]
        rw [this]; exact hinv2.rep_stuck
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

/-! ## `eo::list_len` -/

/-- logos's `list_len_rec` counts the elements of a list given by its end. -/
theorem list_len_rec_eoList {xf xr : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck) :
    ∀ ys, Eo.__eo_list_len_rec (eoList xf xr ys) = Eo.Term.Numeral ys.length := by
  intro ys
  induction ys with
  | nil =>
    simp only [eoList]
    unfold Eo.__eo_list_len_rec
    split <;> simp_all
  | cons y ys ih =>
    simp only [eoList]
    rw [Eo.__eo_list_len_rec.eq_def]
    simp [ih, Eo.__eo_add, SmtEval.native_zplus, Int.add_comm]

/-- `eo::list_len` on handles of an operator and a term: logos's
`__eo_list_len`. -/
theorem Store.builtin_spec_list_len (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b : Term} {xf xa : Eo.Term} (hargs : args.val = [a, b])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListLength args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_len xf xa)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListLength 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hdef : ∀ y z, Eo.__eo_list_len y z = Eo.__eo_requires (Eo.__eo_is_list y z)
      (Eo.Term.Boolean true) (Eo.__eo_list_len_rec z) := fun _ _ => rfl
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
      have : Eo.__eo_list_len Eo.Term.Stuck xa = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_len xf Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
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
        have : Eo.__eo_list_len xf xa = Eo.Term.Stuck := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
          num.Integer.from_usize_spec]
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hval : Eo.__eo_list_len xf xa = Eo.Term.Numeral ys.length := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend,
            list_len_rec_eoList (is_list_nil_not_apply hn) hxr ys]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        have hl : (alloc.vec.Vec.len tail).val = ys.length := by
          simp [alloc.vec.Vec.len]; exact hys.length_eq
        unfold Store.numeral
        rw [hval]
        apply WP.dspec_mono (Store.literal_numeral_spec s1 ((alloc.vec.Vec.len tail).val) hinv1 h64)
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t => simp only at hr2 ⊢; rw [← hl]; exact_mod_cast hr2

/-! ## `eo::list_rev` -/

/-- `reversed`: the vector with the first `i` elements of the slice after
it, last first. -/
theorem reversed_loop_spec (xs : Slice Term) :
    ∀ (out : alloc.vec.Vec Term) (i : Std.Usize), i.val ≤ xs.length →
      out.val.length + i.val < Usize.max →
      reversed_loop xs out i ⦃ r => r.val = out.val ++ (xs.val.take i.val).reverse ⦄div := by
  apply reversed_loop.fixpoint_induct xs
    (motive := fun loop => ∀ (out : alloc.vec.Vec Term) (i : Std.Usize), i.val ≤ xs.length →
      out.val.length + i.val < Usize.max →
      loop out i ⦃ r => r.val = out.val ++ (xs.val.take i.val).reverse ⦄div)
  · prove_adm
  · intro loop ih out i hi hcap
    simp only
    split
    · rename_i hpos
      step as ⟨i1, hi1⟩
      have hlt : i1.val < xs.val.length := by simp only [Slice.length] at hi; scalar_tac
      step as ⟨t, ht⟩
      have hcap1 : out.val.length < Usize.max := by scalar_tac
      step with alloc.vec.Vec.push_spec out t hcap1 as ⟨out1, hout1⟩
      apply WP.dspec_mono (ih out1 i1 (by scalar_tac) (by
        rw [hout1]; simp only [List.length_append, List.length_singleton]; scalar_tac))
      intro r hr
      have hi' : i.val = i1.val + 1 := by scalar_tac
      rw [hr, hout1, hi', ht, List.take_succ_eq_append_getElem hlt]
      simp only [List.reverse_append, List.reverse_singleton, List.append_assoc,
        List.singleton_append]
    · rename_i hz
      simp only [WP.dspec_ok]
      have : i.val = 0 := by scalar_tac
      simp [this]

/-- logos's walk to the nil stops at a nil. -/
theorem get_nil_rec_nil {xf xr : Eo.Term} (hn : Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true)
    (hxr : xr ≠ Eo.Term.Stuck) : Eo.__eo_get_nil_rec xf xr = xr := by
  have hna := is_list_nil_not_apply hn
  have hxf : xf ≠ Eo.Term.Stuck := by
    intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
  unfold Eo.__eo_get_nil_rec
  split <;> simp_all [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]

/-- logos's `list_rev_rec` puts the elements before the accumulator, last
first. -/
theorem rev_rec_eoList {xf xr : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck) :
    ∀ ys acc, acc ≠ Eo.Term.Stuck →
      Eo.__eo_list_rev_rec (eoList xf xr ys) acc = eoList xf acc ys.reverse := by
  intro ys
  induction ys with
  | nil =>
    intro acc hacc
    simp only [eoList, List.reverse_nil]
    unfold Eo.__eo_list_rev_rec
    split <;> simp_all
  | cons y ys ih =>
    intro acc hacc
    simp only [eoList]
    rw [Eo.__eo_list_rev_rec.eq_def]
    simp only [hacc, ne_eq, not_false_eq_true]
    rw [ih _ (by simp), List.reverse_cons, eoList_append]
    rfl

/-- `eo::list_rev` on handles of an operator and a term: logos's
`__eo_list_rev`. -/
theorem Store.builtin_spec_list_rev (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b : Term} {xf xa : Eo.Term} (hargs : args.val = [a, b])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListRev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_rev xf xa)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListRev 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hdef : ∀ y z, Eo.__eo_list_rev y z = Eo.__eo_requires (Eo.__eo_is_list y z)
      (Eo.Term.Boolean true) (Eo.__eo_list_rev_rec z (Eo.__eo_get_nil_rec y z)) := fun _ _ => rfl
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
      have : Eo.__eo_list_rev Eo.Term.Stuck xa = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_rev xf Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
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
        have : Eo.__eo_list_rev xf xa = Eo.Term.Stuck := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have hva : TermValid xa := Store.Rep.valid' hinv hb
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hval : Eo.__eo_list_rev xf xa = eoList xf xr ys.reverse := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend,
            get_nil_rec_eoList hxf xr ys, get_nil_rec_nil hn hxr,
            rev_rec_eoList (is_list_nil_not_apply hn) hxr ys xr hxr]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not,
            eoList_ne_stuck hxr]
        have hmax := hinv.table.hmax
        have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        have hnodes : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
        have htl : tail.val.length ≤ 2 ^ 32 := by
          simp only [alloc.vec.Vec.length] at hsz; omega
        unfold reversed
        step with reversed_loop_spec (alloc.vec.Vec.deref tail)
          (alloc.vec.Vec.with_capacity Term (Slice.len (alloc.vec.Vec.deref tail)))
          (Slice.len (alloc.vec.Vec.deref tail))
          (by simp [Slice.len, Slice.length])
          (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.deref, Slice.len]; omega)
          as ⟨rv, hrv⟩
        have hrv' : rv.val = tail.val.reverse := by
          rw [hrv]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.deref, Slice.len]
        have hall : List.Forall₂ s1.Rep (alloc.vec.Vec.deref rv).val ys.reverse := by
          have : (alloc.vec.Vec.deref rv).val = rv.val := by simp [alloc.vec.Vec.deref]
          rw [this, hrv']
          exact List.forall₂_reverse_iff.mpr hys
        have hny : ∀ y ∈ ys.reverse, y ≠ Eo.Term.Stuck := by
          intro y hy
          exact eoList_valid_elems ys (hxl ▸ hva) y (List.mem_reverse.mp hy)
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s1 (Represents.grows ha hg1) hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref rv)).val = ys.reverse.length := by
          have := hall.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s1 h64 (alloc.vec.Vec.deref rv)
          ys.reverse hall hxf hny hxr s1 rest (Slice.len (alloc.vec.Vec.deref rv)) hinv1
          (Store.Grows.refl s1) (Represents.grows ha hg1) (by omega)
          (by rw [hlenE, List.drop_length]; exact hrest))
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t => simp only at hr2 ⊢; rw [hval]; exact hr2

/-! ## `eo::list_nth` -/

/-- A handle of a numeral holds that numeral's literal. -/
theorem Store.rep_numeral_lit {s : Store} {a : Term} {k : Int}
    (ha : s.Rep a (Eo.Term.Numeral k)) :
    s.nodes.val[a.val]! = TermData.Literal (lit.Lit.Numeral (num.Integer.ofInt k)) := by
  obtain ⟨hh, _⟩ := ha
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
  cases hh with
  | lit _ _ _ hd => exact hd

/-- `object_index` on a handle of a term: the index if the term is a
numeral in `[0, 2^32)`, nothing otherwise. -/
theorem Store.object_index_rep {s : Store} {t : Term} {x : Eo.Term} (ha : s.Rep t x) :
    ∃ o, Store.object_index s t = ok (core.result.Result.Ok o) ∧
      match o with
      | some n => ∃ k : Int, x = Eo.Term.Numeral k ∧ (n.val : Int) = k
      | none => ∀ k : Int, x = Eo.Term.Numeral k → ¬ (0 ≤ k ∧ k < 2 ^ 32) := by
  have hnum : ∀ k, x = Eo.Term.Numeral k →
      s.nodes.val[t.val]! = TermData.Literal (lit.Lit.Numeral (num.Integer.ofInt k)) := by
    intro k hk; subst hk; exact Store.rep_numeral_lit ha
  unfold Store.object_index
  rw [Store.view_eq]
  simp only [ha.lt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  cases hd : s.nodes.val[t.val]! with
  | Literal l =>
    simp only
    rcases Store.rep_lit ha hd with ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ |
        ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl, _⟩
    · exact ⟨none, rfl, fun k h => by cases h⟩
    · simp only [num.Integer.fits_u32_spec, num.Integer.toInt_ofInt, Std.bind_ok]
      by_cases hk : 0 ≤ i ∧ i < 2 ^ 32
      · obtain ⟨r, hr, hv⟩ := num.Integer.to_u32_spec (num.Integer.ofInt i)
        simp only [hk, decide_true, ite_true, hr, Std.bind_ok]
        refine ⟨some r, rfl, i, rfl, ?_⟩
        rw [hv, if_pos (by rw [num.Integer.toInt_ofInt]; exact hk), num.Integer.toInt_ofInt]
      · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
        exact ⟨none, rfl, fun k h => by cases h; exact hk⟩
    · exact ⟨none, rfl, fun k h => by cases h⟩
    · exact ⟨none, rfl, fun k h => by cases h⟩
    · exact ⟨none, rfl, fun k h => by cases h⟩
  | _ =>
    simp only
    refine ⟨none, rfl, fun k h => ?_⟩
    have := hnum k h
    rw [hd] at this
    cases this

/-- logos's `list_nth_rec` at a numeral: the element at that place, or the
stuck term past the end or below zero. -/
theorem nth_rec_eoList_num {xf xr : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) :
    ∀ (ys : List Eo.Term) (k : Int),
      Eo.__eo_list_nth_rec (eoList xf xr ys) (Eo.Term.Numeral k) =
        if h : 0 ≤ k ∧ k.toNat < ys.length then ys[k.toNat] else Eo.Term.Stuck := by
  intro ys
  induction ys with
  | nil =>
    intro k
    simp only [eoList, List.length_nil, Nat.not_lt_zero, and_false, _root_.dite_false]
    unfold Eo.__eo_list_nth_rec
    split <;> simp_all
  | cons y ys ih =>
    intro k
    simp only [eoList]
    by_cases hk0 : k = 0
    · subst hk0; simp [Eo.__eo_list_nth_rec]
    · have hstep : Eo.__eo_list_nth_rec
            (Eo.Term.Apply (Eo.Term.Apply xf y) (eoList xf xr ys)) (Eo.Term.Numeral k) =
          Eo.__eo_list_nth_rec (eoList xf xr ys)
            (Eo.__eo_add (Eo.Term.Numeral k) (Eo.Term.Numeral (-1))) := by
        simp [Eo.__eo_list_nth_rec, hk0]
      have hadd : Eo.__eo_add (Eo.Term.Numeral k) (Eo.Term.Numeral (-1)) =
          Eo.Term.Numeral (k - 1) := by
        simp [Eo.__eo_add, SmtEval.native_zplus, Int.sub_eq_add_neg]
      rw [hstep, hadd, ih (k - 1)]
      by_cases hneg : k < 0
      · have h1 : ¬ (0 ≤ k - 1 ∧ (k - 1).toNat < ys.length) := by omega
        have h2 : ¬ (0 ≤ k ∧ k.toNat < (y :: ys).length) := by omega
        rw [dif_neg h1, dif_neg h2]
      · have hpos : 0 < k := by omega
        have hidx : k.toNat = (k - 1).toNat + 1 := by omega
        by_cases hlt : (k - 1).toNat < ys.length
        · have h1 : 0 ≤ k - 1 ∧ (k - 1).toNat < ys.length := ⟨by omega, hlt⟩
          have h2 : 0 ≤ k ∧ k.toNat < (y :: ys).length := by
            simp only [List.length_cons]; omega
          rw [dif_pos h1, dif_pos h2]
          simp only [hidx, List.getElem_cons_succ]
        · have h1 : ¬ (0 ≤ k - 1 ∧ (k - 1).toNat < ys.length) := by omega
          have h2 : ¬ (0 ≤ k ∧ k.toNat < (y :: ys).length) := by
            simp only [List.length_cons]; omega
          rw [dif_neg h1, dif_neg h2]

/-- logos's `list_nth_rec` at what is not a numeral (and not stuck): the
stuck term. -/
theorem nth_rec_eoList_nonnum {xf xr : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) :
    ∀ (ys : List Eo.Term) (xi : Eo.Term), xi ≠ Eo.Term.Stuck →
      (∀ k, xi ≠ Eo.Term.Numeral k) →
      Eo.__eo_list_nth_rec (eoList xf xr ys) xi = Eo.Term.Stuck := by
  intro ys
  induction ys with
  | nil =>
    intro xi hs hn
    simp only [eoList]
    unfold Eo.__eo_list_nth_rec
    split <;> simp_all
  | cons y ys _ =>
    intro xi hs hn
    simp only [eoList]
    have hadd : Eo.__eo_add xi (Eo.Term.Numeral (-1)) = Eo.Term.Stuck := by
      unfold Eo.__eo_add; split <;> simp_all
    rw [Eo.__eo_list_nth_rec.eq_def]
    split
    · simp_all
    · exact absurd rfl (hn 0)
    · rw [hadd]; unfold Eo.__eo_list_nth_rec; simp
    · simp_all

/-- `eo::list_nth` on handles of an operator, a term and an index: logos's
`__eo_list_nth`. -/
theorem Store.builtin_spec_list_nth (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xi : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xi) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListNth args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_nth xf xa xi)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListNth 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hdef : ∀ y z w, Eo.__eo_list_nth y z w = Eo.__eo_requires (Eo.__eo_is_list y z)
      (Eo.Term.Boolean true) (Eo.__eo_list_nth_rec z w) := fun _ _ _ => rfl
  have hrecStuck : ∀ z, Eo.__eo_list_nth_rec z Eo.Term.Stuck = Eo.Term.Stuck := by
    intro z; cases z <;> simp [Eo.__eo_list_nth_rec]
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
      have : Eo.__eo_list_nth Eo.Term.Stuck xa xi = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_nth xf Eo.Term.Stuck xi = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxi : xi = Eo.Term.Stuck
    · subst hxi
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_nth xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hdef, hrecStuck, requires_ite]
        split_ifs <;> rfl
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hxi, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
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
        have : Eo.__eo_list_nth xf xa xi = Eo.Term.Stuck := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h2]
        show generated.part0.Store.list_nth s1 (alloc.vec.Vec.deref tail) c ⦃ r s' => _ ⦄div
        have hval : Eo.__eo_list_nth xf xa xi = Eo.__eo_list_nth_rec (eoList xf xr ys) xi := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        have hna := is_list_nil_not_apply hn
        have hmax := hinv.table.hmax
        have hnodes : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
        have hly : ys.length ≤ 2 ^ 32 := by
          have := hys.length_eq; simp only [alloc.vec.Vec.length] at hsz; omega
        unfold generated.part0.Store.list_nth
        obtain ⟨o, ho, hoP⟩ := Store.object_index_rep (Represents.grows hc hg1)
        rw [ho]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        cases o with
        | none =>
          simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv1, hg1, ?_⟩
          have : Eo.__eo_list_nth_rec (eoList xf xr ys) xi = Eo.Term.Stuck := by
            by_cases hnum : ∃ k, xi = Eo.Term.Numeral k
            · obtain ⟨k, rfl⟩ := hnum
              have hk := hoP k rfl
              rw [nth_rec_eoList_num hna ys k, dif_neg]
              intro h; apply hk; refine ⟨h.1, ?_⟩; omega
            · exact nth_rec_eoList_nonnum hna ys xi hxi (fun k h => hnum ⟨k, h⟩)
          rw [hval, this]; exact hinv1.rep_stuck
        | some m =>
          obtain ⟨k, rfl, hmk⟩ := hoP
          have hk0 : 0 ≤ k := by omega
          have hnat : k.toNat = m.val := by omega
          simp only [lift, Std.bind_ok]
          have hi : ((UScalar.cast UScalarTy.Usize m : Std.Usize) : Nat) = (m.val : Nat) := by
            simp
          generalize hio : (UScalar.cast UScalarTy.Usize m : Std.Usize) = i at hi ⊢
          have hlenT := hys.length_eq
          split
          · rename_i hlt
            have hil : i.val < tail.val.length := by
              have : i.val < (Slice.len (alloc.vec.Vec.deref tail)).val := hlt
              simpa [Slice.len, alloc.vec.Vec.deref] using this
            have hlt' : m.val < ys.length := by omega
            have hidx : Slice.index_usize (alloc.vec.Vec.deref tail) i =
                ok (tail.val[m.val]'(by omega)) := by
              simp [Slice.index_usize, alloc.vec.Vec.deref, hil, hi,
                List.getElem?_eq_getElem (show m.val < tail.val.length by omega)]
            simp only [hidx, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv1, hg1, ?_⟩
            have : Eo.__eo_list_nth_rec (eoList xf xr ys) (Eo.Term.Numeral k) =
                ys[m.val]'hlt' := by
              rw [nth_rec_eoList_num hna ys k, dif_pos ⟨hk0, by omega⟩]
              simp only [hnat]
            rw [hval, this]
            exact hys.get _ _
          · rename_i hge
            simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv1, hg1, ?_⟩
            have hge' : ¬ m.val < ys.length := by
              intro hlt
              apply hge
              show i.val < (Slice.len (alloc.vec.Vec.deref tail)).val
              simp [Slice.len, alloc.vec.Vec.deref]; omega
            have : Eo.__eo_list_nth_rec (eoList xf xr ys) (Eo.Term.Numeral k) = Eo.Term.Stuck := by
              rw [nth_rec_eoList_num hna ys k, dif_neg]
              intro h; exact hge' (by omega)
            rw [hval, this]; exact hinv1.rep_stuck

/-! ## `eo::list_find` -/

/-- `position_loop`: the first place below `i` where the slice has `x`, or
`found` if there is none. -/
theorem position_loop_spec (xs : Slice Term) (x : Term) :
    ∀ (found : Option Std.Usize) (i : Std.Usize), i.val ≤ xs.length →
      position_loop xs x found i ⦃ r =>
        (r.map (·.val)) = ((xs.val.take i.val).findIdx? (fun t => decide (t = x))).or (found.map (·.val)) ⦄div := by
  apply position_loop.fixpoint_induct xs x
    (motive := fun loop => ∀ (found : Option Std.Usize) (i : Std.Usize), i.val ≤ xs.length →
      loop found i ⦃ r =>
        (r.map (·.val)) = ((xs.val.take i.val).findIdx? (fun t => decide (t = x))).or (found.map (·.val)) ⦄div)
  · prove_adm
  · intro loop ih found i hi
    simp only
    split
    · rename_i hpos
      step as ⟨i1, hi1⟩
      have hlt : i1.val < xs.val.length := by simp only [Slice.length] at hi; scalar_tac
      step as ⟨t, ht⟩
      have hi' : i.val = i1.val + 1 := by scalar_tac
      -- the take of i is the take of i1 and the element at i1
      have htake : xs.val.take i.val = xs.val.take i1.val ++ [xs.val[i1.val]] := by
        rw [hi', List.take_succ_eq_append_getElem hlt]
      have hlen1 : (xs.val.take i1.val).length = i1.val := by
        simp only [List.length_take]; omega
      simp only [Term.Insts.CoreCmpPartialEqTerm.eq, Std.bind_ok]
      subst ht
      have hle1 : i1.val ≤ xs.length := by simp only [Slice.length] at hi ⊢; omega
      by_cases htx : (xs.val)[i1.val] = x
      · simp only [htx, decide_true, ite_true]
        apply WP.dspec_mono (ih (some i1) i1 hle1)
        intro r hr
        rw [hr, htake, List.findIdx?_append, hlen1]
        simp [htx]
      · simp only [htx, decide_false, Bool.false_eq_true, ite_false]
        apply WP.dspec_mono (ih found i1 hle1)
        intro r hr
        rw [hr, htake, List.findIdx?_append]
        simp [htx]
    · rename_i hz
      simp only [WP.dspec_ok]
      have : i.val = 0 := by scalar_tac
      simp [this]

/-- logos's `list_find_rec` from a numeral `k`: `k` plus the first place of
`z`, or -1. -/
theorem find_rec_eoList {xf xr z : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck)
    (hz : z ≠ Eo.Term.Stuck) :
    ∀ (ys : List Eo.Term), (∀ y ∈ ys, y ≠ Eo.Term.Stuck) → ∀ k : Int,
      Eo.__eo_list_find_rec (eoList xf xr ys) z (Eo.Term.Numeral k) =
        match ys.findIdx? (fun y => decide (y = z)) with
        | some j => Eo.Term.Numeral (k + j)
        | none => Eo.Term.Numeral (-1) := by
  intro ys
  induction ys with
  | nil =>
    intro _ k
    simp only [eoList, List.findIdx?_nil]
    unfold Eo.__eo_list_find_rec
    split <;> simp_all
  | cons y ys ih =>
    intro hny k
    simp only [eoList]
    have hy : y ≠ Eo.Term.Stuck := hny y (by simp)
    have heq : Eo.__eo_eq y z = Eo.Term.Boolean (decide (y = z)) := by
      unfold Eo.__eo_eq; split <;> simp_all [Eo.native_teq, eq_comm]
    have hadd : Eo.__eo_add (Eo.Term.Numeral k) (Eo.Term.Numeral 1) =
        Eo.Term.Numeral (k + 1) := by
      simp [Eo.__eo_add, SmtEval.native_zplus]
    have hstep : Eo.__eo_list_find_rec (Eo.Term.Apply (Eo.Term.Apply xf y) (eoList xf xr ys)) z
          (Eo.Term.Numeral k) =
        Eo.__eo_ite (Eo.__eo_eq y z) (Eo.Term.Numeral k)
          (Eo.__eo_list_find_rec (eoList xf xr ys) z
            (Eo.__eo_add (Eo.Term.Numeral k) (Eo.Term.Numeral 1))) := by
      rw [Eo.__eo_list_find_rec.eq_def]; simp
    rw [hstep, heq, hadd, List.findIdx?_cons]
    by_cases hyz : y = z
    · simp [hyz, Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq]
    · rw [ih (fun w hw => hny w (by simp [hw])) (k + 1)]
      simp only [hyz, decide_false, Bool.false_eq_true, ite_false]
      simp only [Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq]
      cases List.findIdx? (fun y => decide (y = z)) ys with
      | none => simp
      | some j =>
        have hkj : k + 1 + (j : Int) = k + ((j + 1 : Nat) : Int) := by push_cast; omega
        simp [hkj]


/-- Searching the handles of a list for a handle is searching its terms for
the term the handle stands for. -/
theorem findIdx_rep {s : Store} (hinv : s.Inv) {c : Term} {xi : Eo.Term} (hc : s.Rep c xi) :
    ∀ {ts : List Term} {ys : List Eo.Term}, List.Forall₂ s.Rep ts ys →
      ts.findIdx? (fun t => decide (t = c)) = ys.findIdx? (fun y => decide (y = xi))
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.findIdx?_cons, List.findIdx?_cons, findIdx_rep hinv hc hs]
    simp [Store.Rep.eq_iff hinv h hc]

/-- `eo::list_find` on handles of an operator, a list and a term: logos's
`__eo_list_find`. -/
theorem Store.builtin_spec_list_find (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xi : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xi) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListFind args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_find xf xa xi)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListFind 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hdef : ∀ y z w, Eo.__eo_list_find y z w = Eo.__eo_requires (Eo.__eo_is_list y z)
      (Eo.Term.Boolean true) (Eo.__eo_list_find_rec z w (Eo.Term.Numeral 0)) := fun _ _ _ => rfl
  have hrecStuck : ∀ z, Eo.__eo_list_find_rec z Eo.Term.Stuck (Eo.Term.Numeral 0) =
      Eo.Term.Stuck := by
    intro z; cases z <;> simp [Eo.__eo_list_find_rec]
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
      have : Eo.__eo_list_find Eo.Term.Stuck xa xi = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_find xf Eo.Term.Stuck xi = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxi : xi = Eo.Term.Stuck
    · subst hxi
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_find xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hdef, hrecStuck, requires_ite]
        split_ifs <;> rfl
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hxi, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
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
        have : Eo.__eo_list_find xf xa xi = Eo.Term.Stuck := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h2]
        have hva : TermValid xa := Store.Rep.valid' hinv hb
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hxl ▸ hva)
        have hval : Eo.__eo_list_find xf xa xi =
            Eo.__eo_list_find_rec (eoList xf xr ys) xi (Eo.Term.Numeral 0) := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        rw [find_rec_eoList (is_list_nil_not_apply hn) hxr hxi ys hny 0] at hval
        have hidx := findIdx_rep hinv1 (Represents.grows hc hg1) hys
        unfold position
        step with position_loop_spec (alloc.vec.Vec.deref tail) c none
          (Slice.len (alloc.vec.Vec.deref tail)) (by simp [Slice.len, Slice.length])
          as ⟨o, ho⟩
        have ho' : o.map (·.val) = ys.findIdx? (fun y => decide (y = xi)) := by
          rw [ho, ← hidx]; simp [Slice.len, Slice.length, alloc.vec.Vec.deref]
        cases o with
        | none =>
          simp only [num.Integer.one_spec, num.Integer.neg_spec, num.Integer.toInt_ofInt,
            Std.bind_ok]
          have hnone : ys.findIdx? (fun y => decide (y = xi)) = none := by
            rw [← ho']; rfl
          rw [hnone] at hval
          unfold Store.numeral
          apply WP.dspec_mono (Store.literal_numeral_spec s1 (-1) hinv1 h64)
          rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
          refine ⟨hinv2, hg1.trans hg2, ?_⟩
          cases r2 with
          | Err e => trivial
          | Ok t => simp only at hr2 ⊢; rw [hval]; exact hr2
        | some i =>
          simp only [num.Integer.from_usize_spec, Std.bind_ok]
          have hsome : ys.findIdx? (fun y => decide (y = xi)) = some i.val := by
            rw [← ho']; rfl
          rw [hsome] at hval
          unfold Store.numeral
          apply WP.dspec_mono (Store.literal_numeral_spec s1 (i.val : Int) hinv1 h64)
          rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
          refine ⟨hinv2, hg1.trans hg2, ?_⟩
          cases r2 with
          | Err e => trivial
          | Ok t => simp only at hr2 ⊢; rw [hval]; simpa using hr2


/-! ## `eo::list_erase` -/

/-- `without_first_loop`: what is already out, then the rest of the slice
from `i`, without its first `x` unless one was erased already. -/
theorem without_first_loop_spec (xs : Slice Term) (x : Term) :
    ∀ (out : alloc.vec.Vec Term) (erased : Bool) (i : Std.Usize), i.val ≤ xs.length →
      out.val.length + (xs.length - i.val) < Usize.max →
      without_first_loop xs x out erased i ⦃ r =>
        r.val = out.val ++ (if erased then xs.val.drop i.val
          else (xs.val.drop i.val).eraseP (fun t => decide (t = x))) ⦄div := by
  apply without_first_loop.fixpoint_induct xs x
    (motive := fun loop => ∀ (out : alloc.vec.Vec Term) (erased : Bool) (i : Std.Usize),
      i.val ≤ xs.length → out.val.length + (xs.length - i.val) < Usize.max →
      loop out erased i ⦃ r =>
        r.val = out.val ++ (if erased then xs.val.drop i.val
          else (xs.val.drop i.val).eraseP (fun t => decide (t = x))) ⦄div)
  · prove_adm
  · intro loop ih out erased i hi hcap
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < xs.val.length := by simp [Slice.len, Slice.length] at hlt ⊢; scalar_tac
      have hdrop : xs.val.drop i.val = xs.val[i.val] :: xs.val.drop (i.val + 1) :=
        List.drop_eq_getElem_cons hlt'
      have hle : i.val + 1 ≤ xs.length := by simp only [Slice.length] at hi ⊢; omega
      cases erased with
      | true =>
        simp only [ite_true]
        step as ⟨t, ht⟩
        have hcap1 : out.val.length < Usize.max := by simp only [Slice.length] at hcap; omega
        step with alloc.vec.Vec.push_spec out t hcap1 as ⟨out1, hout1⟩
        step as ⟨i2, hi2⟩
        apply WP.dspec_mono (ih out1 true i2 (by scalar_tac) (by
          rw [hout1]; simp only [List.length_append, List.length_singleton, Slice.length] at hcap ⊢
          scalar_tac))
        intro r hr
        rw [hr, hout1, hdrop, hi2, ht]
        simp
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        step as ⟨t, ht⟩
        simp only [Term.Insts.CoreCmpPartialEqTerm.eq, Std.bind_ok]
        subst ht
        by_cases htx : xs.val[i.val] = x
        · simp only [htx, decide_true, ite_true, Std.bind_ok]
          step as ⟨i2, hi2⟩
          apply WP.dspec_mono (ih out true i2 (by scalar_tac) (by
            simp only [Slice.length] at hcap ⊢; scalar_tac))
          intro r hr
          rw [hr, hdrop, hi2]
          simp [htx]
        · simp only [htx, decide_false, Bool.false_eq_true, ite_false, Std.bind_ok]
          have hcap1 : out.val.length < Usize.max := by simp only [Slice.length] at hcap; omega
          step with alloc.vec.Vec.push_spec out _ hcap1 as ⟨out1, hout1⟩
          step as ⟨i2, hi2⟩
          apply WP.dspec_mono (ih out1 false i2 (by scalar_tac) (by
            rw [hout1]; simp only [List.length_append, List.length_singleton, Slice.length] at hcap ⊢
            scalar_tac))
          intro r hr
          rw [hr, hout1, hi2, hdrop,
            List.eraseP_cons_of_neg (p := fun t => decide (t = x)) (by simpa using htx)]
          simp
    · rename_i hge
      simp only [WP.dspec_ok]
      have : xs.val.length ≤ i.val := by simp [Slice.len, Slice.length] at hge ⊢; scalar_tac
      simp [List.drop_eq_nil_of_le this]

/-- logos's `list_erase_rec`: the list without the first place of `z`, ending
in the same nil. -/
theorem erase_rec_eoList {xf xr z : Eo.Term}
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck)
    (hz : z ≠ Eo.Term.Stuck) :
    ∀ (ys : List Eo.Term), (∀ y ∈ ys, y ≠ Eo.Term.Stuck) →
      Eo.__eo_list_erase_rec (eoList xf xr ys) z =
        eoList xf xr (ys.eraseP (fun y => decide (y = z))) := by
  intro ys
  induction ys with
  | nil =>
    intro _
    simp only [eoList, List.eraseP_nil]
    unfold Eo.__eo_list_erase_rec
    split <;> simp_all
  | cons y ys ih =>
    intro hny
    have hy : y ≠ Eo.Term.Stuck := hny y (by simp)
    have heq : Eo.__eo_eq y z = Eo.Term.Boolean (decide (y = z)) := by
      unfold Eo.__eo_eq; split <;> simp_all [Eo.native_teq, eq_comm]
    have hstep : Eo.__eo_list_erase_rec (Eo.Term.Apply (Eo.Term.Apply xf y) (eoList xf xr ys)) z =
        Eo.__eo_ite (Eo.__eo_eq y z) (eoList xf xr ys)
          (Eo.__eo_mk_apply (Eo.Term.Apply xf y) (Eo.__eo_list_erase_rec (eoList xf xr ys) z)) := by
      rw [Eo.__eo_list_erase_rec.eq_def]; simp
    simp only [eoList]
    rw [hstep, heq, ih (fun w hw => hny w (by simp [hw]))]
    by_cases hyz : y = z
    · simp [hyz, Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq]
    · have hne := eoList_ne_stuck (xf := xf) hxr (ys.eraseP (fun y => decide (y = z)))
      simp [hyz, Eo.__eo_ite, SmtEval.native_ite, Eo.native_teq, List.eraseP_cons_of_neg,
        Eo.__eo_mk_apply, hne, eoList]

/-- Erasing a handle from a list of handles is erasing the term it stands for
from their terms. -/
theorem eraseP_rep {s : Store} (hinv : s.Inv) {c : Term} {xi : Eo.Term} (hc : s.Rep c xi) :
    ∀ {ts : List Term} {ys : List Eo.Term}, List.Forall₂ s.Rep ts ys →
      List.Forall₂ s.Rep (ts.eraseP (fun t => decide (t = c)))
        (ys.eraseP (fun y => decide (y = xi)))
  | _, _, .nil => by simp
  | _, _, .cons (a := t) (b := y) h hs => by
    by_cases hty : y = xi
    · have htc : t = c := (Store.Rep.eq_iff hinv h hc).mpr hty
      simp [htc, hty, hs]
    · have htc : ¬ t = c := fun e => hty ((Store.Rep.eq_iff hinv h hc).mp e)
      rw [List.eraseP_cons_of_neg (p := fun t => decide (t = c)) (by simpa using htc),
        List.eraseP_cons_of_neg (p := fun y => decide (y = xi)) (by simpa using hty)]
      exact List.Forall₂.cons h (eraseP_rep hinv hc hs)

/-- `eo::list_erase` on handles of an operator, a list and a term: logos's
`__eo_list_erase`. -/
theorem Store.builtin_spec_list_erase (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xi : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xi) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListErase args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_erase xf xa xi)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListErase 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hdef : ∀ y z w, Eo.__eo_list_erase y z w = Eo.__eo_requires (Eo.__eo_is_list y z)
      (Eo.Term.Boolean true) (Eo.__eo_list_erase_rec z w) := fun _ _ _ => rfl
  have hrecStuck : ∀ z, Eo.__eo_list_erase_rec z Eo.Term.Stuck = Eo.Term.Stuck := by
    intro z; cases z <;> simp [Eo.__eo_list_erase_rec]
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
      have : Eo.__eo_list_erase Eo.Term.Stuck xa xi = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_erase xf Eo.Term.Stuck xi = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxi : xi = Eo.Term.Stuck
    · subst hxi
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_erase xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hdef, hrecStuck, requires_ite]
        split_ifs <;> rfl
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hxi, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
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
        have : Eo.__eo_list_erase xf xa xi = Eo.Term.Stuck := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h2]
        have hva : TermValid xa := Store.Rep.valid' hinv hb
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hxl ▸ hva)
        have hval : Eo.__eo_list_erase xf xa xi = eoList xf xr (ys.eraseP (fun y => decide (y = xi))) := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend,
            erase_rec_eoList (is_list_nil_not_apply hn) hxr hxi ys hny]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        have hmax := hinv.table.hmax
        have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        have hnodes : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
        have htl : tail.val.length ≤ 2 ^ 32 := by
          simp only [alloc.vec.Vec.length] at hsz; omega
        unfold without_first
        step with without_first_loop_spec (alloc.vec.Vec.deref tail) c
          (alloc.vec.Vec.with_capacity Term (Slice.len (alloc.vec.Vec.deref tail))) false 0#usize
          (by simp)
          (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.deref, Slice.len, Slice.length]; omega)
          as ⟨rv, hrv⟩
        have hrv' : rv.val = tail.val.eraseP (fun t => decide (t = c)) := by
          rw [hrv]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.deref]
        have hall : List.Forall₂ s1.Rep (alloc.vec.Vec.deref rv).val (ys.eraseP (fun y => decide (y = xi))) := by
          have : (alloc.vec.Vec.deref rv).val = rv.val := by simp [alloc.vec.Vec.deref]
          rw [this, hrv']
          exact eraseP_rep hinv1 (Represents.grows hc hg1) hys
        have hny' : ∀ y ∈ (ys.eraseP (fun y => decide (y = xi))), y ≠ Eo.Term.Stuck :=
          fun y hy => hny y (List.mem_of_mem_eraseP hy)
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s1 (Represents.grows ha hg1) hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref rv)).val = (ys.eraseP (fun y => decide (y = xi))).length := by
          have := hall.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s1 h64 (alloc.vec.Vec.deref rv)
          (ys.eraseP (fun y => decide (y = xi))) hall hxf hny' hxr s1 rest (Slice.len (alloc.vec.Vec.deref rv)) hinv1
          (Store.Grows.refl s1) (Represents.grows ha hg1) (by omega)
          (by rw [hlenE, List.drop_length]; exact hrest))
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t => simp only at hr2 ⊢; rw [hval]; exact hr2


/-! ## `eo::list_setof` -/

/-- A handle is among handles exactly when the term it stands for is among
theirs. -/
theorem rep_mem_iff {s : Store} (hinv : s.Inv) {t : Term} {y : Eo.Term} (ht : s.Rep t y) :
    ∀ {ts : List Term} {ys : List Eo.Term}, List.Forall₂ s.Rep ts ys → (t ∈ ts ↔ y ∈ ys)
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    simp only [List.mem_cons]
    rw [Store.Rep.eq_iff hinv ht h, rep_mem_iff hinv ht hs]

theorem foldl_firstOccStep_rep {s : Store} (hinv : s.Inv) :
    ∀ {ts : List Term} {ys : List Eo.Term}, List.Forall₂ s.Rep ts ys →
      ∀ {at_ : List Term} {ay : List Eo.Term}, List.Forall₂ s.Rep at_ ay →
      List.Forall₂ s.Rep (ts.foldl firstOccStep at_) (ys.foldl firstOccStep ay)
  | _, _, .nil, _, _, hacc => hacc
  | _, _, .cons (a := t) (b := y) h hs, at_, ay, hacc => by
    simp only [List.foldl_cons]
    apply foldl_firstOccStep_rep hinv hs
    unfold firstOccStep
    by_cases hy : y ∈ ay
    · have ht : t ∈ at_ := (rep_mem_iff hinv h hacc).mpr hy
      simp [ht, hy, hacc]
    · have ht : t ∉ at_ := fun e => hy ((rep_mem_iff hinv h hacc).mp e)
      simp only [ht, hy, ite_false]
      exact List.rel_append hacc (List.Forall₂.cons h List.Forall₂.nil)

theorem firstOcc_rep {s : Store} (hinv : s.Inv) {ts : List Term} {ys : List Eo.Term}
    (h : List.Forall₂ s.Rep ts ys) : List.Forall₂ s.Rep (firstOcc ts) (firstOcc ys) :=
  foldl_firstOccStep_rep hinv h List.Forall₂.nil

theorem setofL_mem {α : Type} [DecidableEq α] {y : α} :
    ∀ {l : List α}, y ∈ setofL l → y ∈ l
  | [], h => by simp [setofL] at h
  | x :: l, h => by
    simp only [setofL, List.mem_cons, List.mem_filter] at h
    rcases h with h | ⟨h, -⟩
    · simp [h]
    · exact List.mem_cons_of_mem _ (setofL_mem h)

/-- logos's `list_erase_all_rec`: the list without `z`, ending in the same
nil. -/
theorem erase_all_rec_eoList {xf xr z : Eo.Term} (hxf : xf ≠ Eo.Term.Stuck)
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck)
    (hz : z ≠ Eo.Term.Stuck) :
    ∀ (ys : List Eo.Term), (∀ y ∈ ys, y ≠ Eo.Term.Stuck) →
      Eo.__eo_list_erase_all_rec (eoList xf xr ys) z =
        eoList xf xr (ys.filter (fun y => decide (y ≠ z))) := by
  intro ys
  induction ys with
  | nil =>
    intro _
    simp only [eoList, List.filter_nil]
    unfold Eo.__eo_list_erase_all_rec
    split <;> simp_all
  | cons y ys ih =>
    intro hny
    have hy : y ≠ Eo.Term.Stuck := hny y (by simp)
    have heq : Eo.__eo_eq z y = Eo.Term.Boolean (decide (y = z)) := by
      unfold Eo.__eo_eq; split <;> simp_all [Eo.native_teq]
    have hrest := ih (fun w hw => hny w (by simp [hw]))
    have hne : ∀ l, eoList xf xr l ≠ Eo.Term.Stuck := eoList_ne_stuck hxr
    simp only [eoList]
    rw [Eo.__eo_list_erase_all_rec.eq_def]
    simp only [hrest, heq]
    by_cases hyz : y = z
    · simp [hyz, Eo.__eo_not, SmtEval.native_not, Eo.__eo_prepend_if, hne, hxf, hz]
    · simp [hyz, Eo.__eo_not, SmtEval.native_not, Eo.__eo_prepend_if, hne, hxf, hy, eoList]

/-- logos's `list_setof_rec`: `setofL` of the elements, ending in the same
nil. -/
theorem setof_rec_eoList {xf xr : Eo.Term} (hxf : xf ≠ Eo.Term.Stuck)
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck) :
    ∀ (ys : List Eo.Term), (∀ y ∈ ys, y ≠ Eo.Term.Stuck) →
      Eo.__eo_list_setof_rec (eoList xf xr ys) = eoList xf xr (setofL ys) := by
  intro ys
  induction ys with
  | nil =>
    intro _
    simp only [eoList, setofL]
    unfold Eo.__eo_list_setof_rec
    split <;> simp_all
  | cons y ys ih =>
    intro hny
    have hy : y ≠ Eo.Term.Stuck := hny y (by simp)
    have hys : ∀ w ∈ ys, w ≠ Eo.Term.Stuck := fun w hw => hny w (by simp [hw])
    have hset : ∀ w ∈ setofL ys, w ≠ Eo.Term.Stuck := fun w hw => hys w (setofL_mem hw)
    have hne : ∀ l, eoList xf xr l ≠ Eo.Term.Stuck := eoList_ne_stuck hxr
    simp only [eoList, setofL]
    rw [Eo.__eo_list_setof_rec.eq_def]
    simp only [ih hys, erase_all_rec_eoList hxf hna hxr hy (setofL ys) hset]
    simp [Eo.__eo_mk_apply, hne]

/-- `eo::list_setof` on handles of an operator and a list: logos's
`__eo_list_setof`. -/
theorem Store.builtin_spec_list_setof (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b : Term} {xf xa : Eo.Term} (hargs : args.val = [a, b])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hinv : s.Inv) (h64 : Platform64)
    (hrem : s.remaining ≤ n) (hleft : NotLeftNested xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListSetof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_setof xf xa)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListSetof 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hdef : ∀ y z, Eo.__eo_list_setof y z = Eo.__eo_requires (Eo.__eo_is_list y z)
      (Eo.Term.Boolean true) (Eo.__eo_list_setof_rec z) := fun _ _ => rfl
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
      have : Eo.__eo_list_setof Eo.Term.Stuck xa = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_setof xf Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hdef]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
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
        have : Eo.__eo_list_setof xf xa = Eo.Term.Stuck := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have hva : TermValid xa := Store.Rep.valid' hinv hb
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hxl ▸ hva)
        have hval : Eo.__eo_list_setof xf xa = eoList xf xr (setofL ys) := by
          rw [hdef, hxl, is_list_eoList ys hxf (by rw [← hxl]; exact hxa) hend,
            setof_rec_eoList hxf (is_list_nil_not_apply hn) hxr ys hny]
          simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
        have hmax := hinv.table.hmax
        have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        have hnodes : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
        have htl : tail.val.length ≤ 2 ^ 32 := by
          simp only [alloc.vec.Vec.length] at hsz; omega
        have hlt32 : (alloc.vec.Vec.deref tail).length < 2 ^ 32 := by
          have h1 : tail.val.length ≤ s.nodes.length := by
            simpa [alloc.vec.Vec.length] using hsz
          have h2 : s.nodes.length ≤ U32.max := hmax
          have h3 : (alloc.vec.Vec.deref tail).length = tail.val.length := by
            simp [alloc.vec.Vec.deref, Slice.length]
          rw [h3]; scalar_tac
        step with first_occurrences_spec (alloc.vec.Vec.deref tail) hlt32 h64 as ⟨rv, hrv⟩
        have hall : List.Forall₂ s1.Rep (alloc.vec.Vec.deref rv).val (setofL ys) := by
          have : (alloc.vec.Vec.deref rv).val = rv.val := by simp [alloc.vec.Vec.deref]
          rw [this, hrv, ← firstOcc_eq_setofL]
          exact firstOcc_rep hinv1 (by simpa [alloc.vec.Vec.deref] using hys)
        have hny' : ∀ y ∈ setofL ys, y ≠ Eo.Term.Stuck :=
          fun y hy => hny y (setofL_mem hy)
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s1 (Represents.grows ha hg1) hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref rv)).val = (setofL ys).length := by
          have := hall.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s1 h64 (alloc.vec.Vec.deref rv)
          (setofL ys) hall hxf hny' hxr s1 rest (Slice.len (alloc.vec.Vec.deref rv)) hinv1
          (Store.Grows.refl s1) (Represents.grows ha hg1) (by omega)
          (by rw [hlenE, List.drop_length]; exact hrest))
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t => simp only at hr2 ⊢; rw [hval]; exact hr2


/-! ## `eo::list_diff` and `eo::list_inter` -/

/-- `selectL` on terms: what logos's `list_diff_rec` (`false`) and
`list_inter_rec` (`true`) keep. -/
def selectE (paired : Bool) : List Eo.Term → List Eo.Term → List Eo.Term
  | [], _ => []
  | x :: xs, R => (if decide (x ∈ R) = paired then [x] else []) ++ selectE paired xs (R.erase x)

/-- A list of `f` ending in a nil that is no application of `f`: its
elements are determined. -/
theorem eoList_inj {xf xr : Eo.Term} (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) :
    ∀ l1 l2 : List Eo.Term, eoList xf xr l1 = eoList xf xr l2 → l1 = l2
  | [], [] => fun _ => rfl
  | [], y :: l2 => fun h => absurd h (hna _ _ _)
  | x :: l1, [] => fun h => absurd h.symm (hna _ _ _)
  | x :: l1, y :: l2 => fun h => by
    simp only [eoList, Eo.Term.Apply.injEq] at h
    rw [h.1.2, eoList_inj hna l1 l2 h.2]

theorem erase_eq_eraseP_term (l : List Eo.Term) (x : Eo.Term) :
    l.erase x = l.eraseP (fun y => decide (y = x)) := by
  rw [List.erase_eq_eraseP]; congr 1; funext y
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact eq_comm

theorem eraseP_eq_self_iff {l : List Eo.Term} {x : Eo.Term} :
    l.eraseP (fun y => decide (y = x)) = l ↔ x ∉ l := by
  constructor
  · intro h hx
    have := List.length_eraseP_of_mem (p := fun y => decide (y = x)) hx (decide_eq_true rfl)
    rw [h] at this
    have : 0 < l.length := List.length_pos_of_mem hx
    omega
  · intro hx
    exact List.eraseP_of_forall_not (fun y hy e => hx (by simp at e; exact e ▸ hy))

theorem erase_rep_term (l : List Term) (c : Term) :
    l.erase c = l.eraseP (fun t => decide (t = c)) := by
  rw [List.erase_eq_eraseP]; congr 1; funext y
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact eq_comm

/-- Erasing a handle from handles is erasing its term from their terms. -/
theorem erase_rep {s : Store} (hinv : s.Inv) {c : Term} {xi : Eo.Term} (hc : s.Rep c xi)
    {ts : List Term} {ys : List Eo.Term} (h : List.Forall₂ s.Rep ts ys) :
    List.Forall₂ s.Rep (ts.erase c) (ys.erase xi) := by
  rw [erase_rep_term, erase_eq_eraseP_term]; exact eraseP_rep hinv hc h

/-- `multiset_select` over handles is `selectE` over their terms. -/
theorem selectL_rep {s : Store} (hinv : s.Inv) (paired : Bool) :
    ∀ {xs : List Term} {xs' : List Eo.Term}, List.Forall₂ s.Rep xs xs' →
      ∀ {ys : List Term} {ys' : List Eo.Term}, List.Forall₂ s.Rep ys ys' →
      List.Forall₂ s.Rep (selectL paired xs ys) (selectE paired xs' ys')
  | _, _, .nil, _, _, _ => by simp [selectL, selectE]
  | _, _, .cons (a := x) (b := x') h hs, ys, ys', hys => by
    simp only [selectL, selectE]
    have hmem : (x ∈ ys) ↔ (x' ∈ ys') := rep_mem_iff hinv h hys
    apply List.rel_append
    · by_cases hx : x' ∈ ys'
      · have : x ∈ ys := hmem.mpr hx
        by_cases hp : paired <;> simp [this, hx, hp, h]
      · have : x ∉ ys := fun e => hx (hmem.mp e)
        by_cases hp : paired <;> simp [this, hx, hp, h]
    · exact selectL_rep hinv paired hs (erase_rep hinv h hys)

/-- logos's `list_diff_rec` (`inter` is false) and `list_inter_rec`
(`inter` is true): `selectE` of the elements, ending in the first list's
nil. -/
theorem diff_inter_rec_eoList (inter : Bool) {xf xr xr' : Eo.Term} (hxf : xf ≠ Eo.Term.Stuck)
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck)
    (hna' : ∀ g a c, xr' ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr' : xr' ≠ Eo.Term.Stuck) :
    ∀ (ys zs : List Eo.Term), (∀ y ∈ ys, y ≠ Eo.Term.Stuck) → (∀ z ∈ zs, z ≠ Eo.Term.Stuck) →
      (if inter then Eo.__eo_list_inter_rec (eoList xf xr ys) (eoList xf xr' zs)
       else Eo.__eo_list_diff_rec (eoList xf xr ys) (eoList xf xr' zs)) =
        eoList xf xr (selectE inter ys zs) := by
  intro ys
  induction ys with
  | nil =>
    intro zs _ _
    have hzs := eoList_ne_stuck (xf := xf) hxr' zs
    cases inter <;> simp only [eoList, selectE, Bool.false_eq_true, ite_false, ite_true] <;>
    first
    | (unfold Eo.__eo_list_diff_rec; split <;> simp_all)
    | (unfold Eo.__eo_list_inter_rec; split <;> simp_all)
  | cons y ys ih =>
    intro zs hny hnz
    have hy : y ≠ Eo.Term.Stuck := hny y (by simp)
    have hys : ∀ w ∈ ys, w ≠ Eo.Term.Stuck := fun w hw => hny w (by simp [hw])
    have hzs' : ∀ w ∈ zs.erase y, w ≠ Eo.Term.Stuck := fun w hw => hnz w (List.mem_of_mem_erase hw)
    have hne : ∀ l, eoList xf xr l ≠ Eo.Term.Stuck := eoList_ne_stuck hxr
    have hne' : ∀ l, eoList xf xr' l ≠ Eo.Term.Stuck := eoList_ne_stuck hxr'
    have hv0 : Eo.__eo_list_erase_rec (eoList xf xr' zs) y = eoList xf xr' (zs.erase y) := by
      rw [erase_rec_eoList hna' hxr' hy zs hnz, erase_eq_eraseP_term]
    have heq : Eo.__eo_eq (eoList xf xr' (zs.erase y)) (eoList xf xr' zs) =
        Eo.Term.Boolean (decide (y ∉ zs)) := by
      have hiff : eoList xf xr' zs = eoList xf xr' (zs.erase y) ↔ y ∉ zs := by
        constructor
        · intro h; rw [← eraseP_eq_self_iff, ← erase_eq_eraseP_term]
          exact (eoList_inj hna' _ _ h).symm
        · intro h; rw [List.erase_of_not_mem h]
      unfold Eo.__eo_eq
      split <;> simp_all [Eo.native_teq]
    have hrec := ih (zs.erase y) hys hzs'
    cases inter
    · simp only [Bool.false_eq_true, ite_false] at hrec ⊢
      have hstep : Eo.__eo_list_diff_rec (Eo.Term.Apply (Eo.Term.Apply xf y) (eoList xf xr ys))
          (eoList xf xr' zs) =
          Eo.__eo_prepend_if (Eo.__eo_eq (Eo.__eo_list_erase_rec (eoList xf xr' zs) y)
            (eoList xf xr' zs)) xf y
            (Eo.__eo_list_diff_rec (eoList xf xr ys) (Eo.__eo_list_erase_rec (eoList xf xr' zs) y)) := by
        rw [Eo.__eo_list_diff_rec.eq_def]; simp [hne']
      simp only [eoList]
      rw [hstep, hv0, heq, hrec]
      by_cases hyz : y ∈ zs
      · simp [hyz, Eo.__eo_prepend_if, selectE, hne, hxf, hy]
      · simp [hyz, Eo.__eo_prepend_if, selectE, hne, hxf, hy, eoList, List.erase_of_not_mem hyz]
    · simp only [ite_true] at hrec ⊢
      have hstep : Eo.__eo_list_inter_rec (Eo.Term.Apply (Eo.Term.Apply xf y) (eoList xf xr ys))
          (eoList xf xr' zs) =
          Eo.__eo_prepend_if (Eo.__eo_not (Eo.__eo_eq (Eo.__eo_list_erase_rec (eoList xf xr' zs) y)
            (eoList xf xr' zs))) xf y
            (Eo.__eo_list_inter_rec (eoList xf xr ys) (Eo.__eo_list_erase_rec (eoList xf xr' zs) y)) := by
        rw [Eo.__eo_list_inter_rec.eq_def]; simp [hne']
      simp only [eoList]
      rw [hstep, hv0, heq, hrec]
      by_cases hyz : y ∈ zs
      · simp [hyz, Eo.__eo_not, SmtEval.native_not, Eo.__eo_prepend_if, selectE, hne, hxf, hy,
          eoList]
      · simp [hyz, Eo.__eo_not, SmtEval.native_not, Eo.__eo_prepend_if, selectE, hne, hxf, hy,
          List.erase_of_not_mem hyz]


theorem selectE_mem {paired : Bool} {y : Eo.Term} :
    ∀ {xs R : List Eo.Term}, y ∈ selectE paired xs R → y ∈ xs
  | [], _, h => by simp [selectE] at h
  | x :: xs, R, h => by
    simp only [selectE, List.mem_append] at h
    rcases h with h | h
    · split at h <;> simp_all
    · exact List.mem_cons_of_mem _ (selectE_mem h)

/-- `eo::list_diff` on handles of an operator with one nil and two lists:
logos's `__eo_list_diff`. -/
theorem Store.builtin_spec_list_diff (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xb : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xb)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n)
    (hleft : NotLeftNested xf) (huniq : UniqueNil xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListDiff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_diff xf xa xb)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListDiff 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hcat : ∀ y z, Eo.__eo_list_diff xf y z = Eo.__eo_requires (Eo.__eo_is_list xf y)
      (Eo.Term.Boolean true) (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true)
        (Eo.__eo_list_diff_rec y z)) := fun _ _ => rfl
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
      have : Eo.__eo_list_diff Eo.Term.Stuck xa xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_diff xf Eo.Term.Stuck xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxb : xb = Eo.Term.Stuck
    · subst hxb
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_diff xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
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
    unfold generated.part0.Store.list_selection
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
        have : Eo.__eo_list_diff xf xa xb = Eo.Term.Stuck := by
          rw [hcat]
          rcases hr with h | h
          · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h]
          · by_cases h1 : Eo.__eo_is_list xf xa = Eo.Term.Boolean true
            · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h, h1]
            · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h1]
        rw [this]; exact hinv2.rep_stuck
      | some p =>
        obtain ⟨xsh, ysh, nilh⟩ := p
        obtain ⟨xs, ys, xr, hxs, hys, hnilh, hxl, hyl, hend, hn, hlx', hly'⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have haf := Represents.grows ha hg2
        step with multiset_select_spec (alloc.vec.Vec.deref xsh) (alloc.vec.Vec.deref ysh) false
          (by simp [alloc.vec.Vec.deref, Slice.length]; omega) h64 as ⟨kept, hkept⟩
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hall : List.Forall₂ s2.Rep (alloc.vec.Vec.deref kept).val (selectE false xs ys) := by
          have : (alloc.vec.Vec.deref kept).val = kept.val := by simp [alloc.vec.Vec.deref]
          rw [this, hkept]
          exact selectL_rep hinv2 false (by simpa [alloc.vec.Vec.deref] using hxs)
            (by simpa [alloc.vec.Vec.deref] using hys)
        have hnx : ∀ y ∈ xs, y ≠ Eo.Term.Stuck := eoList_valid_elems xs (hxl ▸ hva)
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hyl ▸ hvb)
        have hnys : ∀ y ∈ selectE false xs ys, y ≠ Eo.Term.Stuck := by
          intro y hy; exact hnx y (selectE_mem hy)
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s2 haf hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref kept)).val = (selectE false xs ys).length := by
          have := hall.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s2 h64 (alloc.vec.Vec.deref kept)
          (selectE false xs ys) hall hxf hnys hxr s2 nilh (Slice.len (alloc.vec.Vec.deref kept)) hinv2
          (Store.Grows.refl s2) haf (by omega)
          (by rw [hlenE, List.drop_length]; exact hnilh))
        rintro ⟨r3, s3⟩ ⟨hinv3, hg3, hr3⟩
        refine ⟨hinv3, hg2.trans hg3, ?_⟩
        cases r3 with
        | Err e => trivial
        | Ok t =>
          simp only at hr3 ⊢
          have hval : Eo.__eo_list_diff xf xa xb = eoList xf xr (selectE false xs ys) := by
            have hrec := diff_inter_rec_eoList false hxf (is_list_nil_not_apply hn) hxr
              (is_list_nil_not_apply hn) hxr xs ys hnx hny
            simp only [Bool.false_eq_true, ite_false, ite_true] at hrec
            rw [hcat, hxl, hyl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hend,
              is_list_eoList ys hxf (by rw [← hyl]; exact hxb) hend, hrec]
            simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
          rw [hval]; exact hr3

/-- `eo::list_inter` on handles of an operator with one nil and two lists:
logos's `__eo_list_inter`. -/
theorem Store.builtin_spec_list_inter (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xb : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xb)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n)
    (hleft : NotLeftNested xf) (huniq : UniqueNil xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListInter args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_inter xf xa xb)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListInter 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hcat : ∀ y z, Eo.__eo_list_inter xf y z = Eo.__eo_requires (Eo.__eo_is_list xf y)
      (Eo.Term.Boolean true) (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true)
        (Eo.__eo_list_inter_rec y z)) := fun _ _ => rfl
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
      have : Eo.__eo_list_inter Eo.Term.Stuck xa xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_inter xf Eo.Term.Stuck xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxb : xb = Eo.Term.Stuck
    · subst hxb
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_inter xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
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
    unfold generated.part0.Store.list_selection
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
        have : Eo.__eo_list_inter xf xa xb = Eo.Term.Stuck := by
          rw [hcat]
          rcases hr with h | h
          · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h]
          · by_cases h1 : Eo.__eo_is_list xf xa = Eo.Term.Boolean true
            · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h, h1]
            · simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h1]
        rw [this]; exact hinv2.rep_stuck
      | some p =>
        obtain ⟨xsh, ysh, nilh⟩ := p
        obtain ⟨xs, ys, xr, hxs, hys, hnilh, hxl, hyl, hend, hn, hlx', hly'⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have haf := Represents.grows ha hg2
        step with multiset_select_spec (alloc.vec.Vec.deref xsh) (alloc.vec.Vec.deref ysh) true
          (by simp [alloc.vec.Vec.deref, Slice.length]; omega) h64 as ⟨kept, hkept⟩
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hall : List.Forall₂ s2.Rep (alloc.vec.Vec.deref kept).val (selectE true xs ys) := by
          have : (alloc.vec.Vec.deref kept).val = kept.val := by simp [alloc.vec.Vec.deref]
          rw [this, hkept]
          exact selectL_rep hinv2 true (by simpa [alloc.vec.Vec.deref] using hxs)
            (by simpa [alloc.vec.Vec.deref] using hys)
        have hnx : ∀ y ∈ xs, y ≠ Eo.Term.Stuck := eoList_valid_elems xs (hxl ▸ hva)
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hyl ▸ hvb)
        have hnys : ∀ y ∈ selectE true xs ys, y ≠ Eo.Term.Stuck := by
          intro y hy; exact hnx y (selectE_mem hy)
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s2 haf hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref kept)).val = (selectE true xs ys).length := by
          have := hall.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s2 h64 (alloc.vec.Vec.deref kept)
          (selectE true xs ys) hall hxf hnys hxr s2 nilh (Slice.len (alloc.vec.Vec.deref kept)) hinv2
          (Store.Grows.refl s2) haf (by omega)
          (by rw [hlenE, List.drop_length]; exact hnilh))
        rintro ⟨r3, s3⟩ ⟨hinv3, hg3, hr3⟩
        refine ⟨hinv3, hg2.trans hg3, ?_⟩
        cases r3 with
        | Err e => trivial
        | Ok t =>
          simp only at hr3 ⊢
          have hval : Eo.__eo_list_inter xf xa xb = eoList xf xr (selectE true xs ys) := by
            have hrec := diff_inter_rec_eoList true hxf (is_list_nil_not_apply hn) hxr
              (is_list_nil_not_apply hn) hxr xs ys hnx hny
            simp only [Bool.false_eq_true, ite_false, ite_true] at hrec
            rw [hcat, hxl, hyl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hend,
              is_list_eoList ys hxf (by rw [← hyl]; exact hxb) hend, hrec]
            simp [hn, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
          rw [hval]; exact hr3


/-! ## `eo::list_minclude` -/

-- logos's `eo::List` constructors, as the generated cases name them.
set_option linter.internalConstructors false

/-- `eo::List` lists: the elements under `__eo_List_cons`, ending in
`__eo_List_nil`. -/
abbrev elemsL (ys : List Eo.Term) : Eo.Term := eoList Eo.Term.__eo_List_cons Eo.Term.__eo_List_nil ys

theorem list_nil_not_apply : ∀ g a c, Eo.Term.__eo_List_nil ≠ Eo.Term.Apply (Eo.Term.Apply g a) c := by
  intro g a c h; cases h

theorem list_nil_ne_stuck : Eo.Term.__eo_List_nil ≠ Eo.Term.Stuck := by intro h; cases h

/-- logos's `get_elements_rec`: the elements as an `eo::List`. -/
theorem get_elements_rec_eoList {xf xr : Eo.Term} (hxf : xf ≠ Eo.Term.Stuck)
    (hna : ∀ g a c, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) c) (hxr : xr ≠ Eo.Term.Stuck) :
    ∀ ys : List Eo.Term, Eo.__eo_get_elements_rec (eoList xf xr ys) = elemsL ys
  | [] => by
    simp only [eoList, elemsL]
    unfold Eo.__eo_get_elements_rec
    split <;> simp_all
  | y :: ys => by
    have hne : ∀ l, elemsL l ≠ Eo.Term.Stuck := eoList_ne_stuck list_nil_ne_stuck
    simp only [eoList, elemsL]
    rw [Eo.__eo_get_elements_rec.eq_def]
    simp only [get_elements_rec_eoList hxf hna hxr ys]
    simp [Eo.__eo_mk_apply, hne, elemsL]

theorem minclude_rec_false {y z : Eo.Term} (hy : y ≠ Eo.Term.Stuck) (hz : z ≠ Eo.Term.Stuck) :
    Eo.__eo_list_minclude_rec y z (Eo.Term.Boolean false) = Eo.Term.Boolean false := by
  unfold Eo.__eo_list_minclude_rec; split <;> simp_all

/-- logos's `list_minclude_rec` on two `eo::List`s: `minclL`. -/
theorem minclude_rec_eoList :
    ∀ (B A : List Eo.Term), (∀ a ∈ A, a ≠ Eo.Term.Stuck) → (∀ b ∈ B, b ≠ Eo.Term.Stuck) →
      Eo.__eo_list_minclude_rec (elemsL A) (elemsL B) (Eo.Term.Boolean true) =
        Eo.Term.Boolean (minclL A B)
  | [], A, _, _ => by
    have hA : elemsL A ≠ Eo.Term.Stuck := eoList_ne_stuck list_nil_ne_stuck A
    simp only [elemsL, eoList, minclL]
    unfold Eo.__eo_list_minclude_rec; split <;> simp_all
  | x :: B, A, hA, hB => by
    have hx : x ≠ Eo.Term.Stuck := hB x (by simp)
    have hB' : ∀ b ∈ B, b ≠ Eo.Term.Stuck := fun b hb => hB b (by simp [hb])
    have hA' : ∀ a ∈ A.erase x, a ≠ Eo.Term.Stuck := fun a ha => hA a (List.mem_of_mem_erase ha)
    have hne : ∀ l, elemsL l ≠ Eo.Term.Stuck := eoList_ne_stuck list_nil_ne_stuck
    have hv0 : Eo.__eo_list_erase_rec (elemsL A) x = elemsL (A.erase x) := by
      rw [erase_rec_eoList list_nil_not_apply list_nil_ne_stuck hx A hA, erase_eq_eraseP_term]
    have heq : Eo.__eo_not (Eo.__eo_eq (elemsL (A.erase x)) (elemsL A)) =
        Eo.Term.Boolean (decide (x ∈ A)) := by
      have hiff : elemsL A = elemsL (A.erase x) ↔ x ∉ A := by
        constructor
        · intro h; rw [← eraseP_eq_self_iff, ← erase_eq_eraseP_term]
          exact (eoList_inj list_nil_not_apply _ _ h).symm
        · intro h; rw [List.erase_of_not_mem h]
      have : Eo.__eo_eq (elemsL (A.erase x)) (elemsL A) = Eo.Term.Boolean (decide (x ∉ A)) := by
        unfold Eo.__eo_eq; split <;> simp_all [Eo.native_teq]
      rw [this]; simp [Eo.__eo_not, SmtEval.native_not]
    have hstep : Eo.__eo_list_minclude_rec (elemsL A) (elemsL (x :: B)) (Eo.Term.Boolean true) =
        Eo.__eo_list_minclude_rec (Eo.__eo_list_erase_rec (elemsL A) x) (elemsL B)
          (Eo.__eo_not (Eo.__eo_eq (Eo.__eo_list_erase_rec (elemsL A) x) (elemsL A))) := by
      rw [Eo.__eo_list_minclude_rec.eq_def]; simp [hne, elemsL, eoList]
    rw [hstep, hv0, heq]
    by_cases hxA : x ∈ A
    · rw [decide_eq_true hxA, minclude_rec_eoList B (A.erase x) hA' hB']
      simp [minclL, hxA]
    · rw [decide_eq_false hxA, minclude_rec_false (hne _) (hne _)]
      simp [minclL, hxA]

/-- A handle's count among handles is its term's count among their terms. -/
theorem count_rep {s : Store} (hinv : s.Inv) {t : Term} {y : Eo.Term} (ht : s.Rep t y) :
    ∀ {ts : List Term} {ys : List Eo.Term}, List.Forall₂ s.Rep ts ys → ts.count t = ys.count y
  | _, _, .nil => by simp
  | _, _, .cons (a := u) (b := z) h hs => by
    rw [List.count_cons, List.count_cons, count_rep hinv ht hs]
    have : (u == t) = (z == y) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact (Store.Rep.eq_iff hinv h ht)
    rw [this]

/-- The runtime's inclusion test over handles is logos's over terms. -/
theorem eraseAll_rep {s : Store} (hinv : s.Inv) {xsh ysh : List Term} {xs ys : List Eo.Term}
    (hx : List.Forall₂ s.Rep xsh xs) (hy : List.Forall₂ s.Rep ysh ys) :
    (eraseAll ysh xsh = []) ↔ minclL xs ys = true := by
  rw [show eraseAll ysh xsh = eraseAllG ysh xsh from rfl, eraseAll_nil_iff, minclL_iff]
  constructor
  · intro h τ
    by_cases hτ : τ ∈ ys
    · obtain ⟨t, -, ht⟩ : ∃ t ∈ ysh, s.Rep t τ := by
        obtain ⟨k, hk, hkτ⟩ := List.mem_iff_getElem.mp hτ
        have hl := hy.length_eq
        refine ⟨ysh[k]'(by omega), List.getElem_mem _, ?_⟩
        rw [← hkτ]; exact List.forall₂_iff_get.mp hy |>.2 k (by omega) hk
      rw [← count_rep hinv ht hy, ← count_rep hinv ht hx]; exact h t
    · simp [List.count_eq_zero_of_not_mem hτ]
  · intro h t
    by_cases ht : t ∈ ysh
    · obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.mp ht
      have hl := hy.length_eq
      have hr : s.Rep t (ys[k]'(by omega)) := by
        rw [← hkt]; exact List.forall₂_iff_get.mp hy |>.2 k hk (by omega)
      rw [count_rep hinv hr hy, count_rep hinv hr hx]; exact h _
    · simp [List.count_eq_zero_of_not_mem ht]


/-- `eo::list_minclude` on handles of an operator with one nil and two lists:
logos's `__eo_list_minclude`. -/
theorem Store.builtin_spec_list_minclude (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xb : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xb)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n)
    (hleft : NotLeftNested xf) (huniq : UniqueNil xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListMinclude args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_minclude xf xa xb)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListMinclude 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hcat : ∀ y z, Eo.__eo_list_minclude xf y z = Eo.__eo_list_minclude_rec
      (Eo.__eo_requires (Eo.__eo_is_list xf y) (Eo.Term.Boolean true) (Eo.__eo_get_elements_rec y))
      (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true) (Eo.__eo_get_elements_rec z))
      (Eo.Term.Boolean true) := fun _ _ => rfl
  have hreqS : ∀ c y, c ≠ Eo.Term.Boolean true →
      Eo.__eo_requires c (Eo.Term.Boolean true) y = Eo.Term.Stuck := by
    intro c y hc; simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hc]
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
      have : Eo.__eo_list_minclude Eo.Term.Stuck xa xb = Eo.Term.Stuck := by
        rw [hcat]; unfold Eo.__eo_list_minclude_rec; split <;> simp_all [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, Eo.__eo_is_list]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_minclude xf Eo.Term.Stuck xb = Eo.Term.Stuck := by
        rw [hcat]; unfold Eo.__eo_list_minclude_rec; split <;> simp_all [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, Eo.__eo_is_list]
      rw [this]; exact hinv.rep_stuck
    by_cases hxb : xb = Eo.Term.Stuck
    · subst hxb
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_minclude xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hcat]; unfold Eo.__eo_list_minclude_rec; split <;> simp_all [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, Eo.__eo_is_list]
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hxb, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
    simp only [h0, h1, h2, Std.bind_ok]
    unfold generated.part0.Store.list_inclusion
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
        have : Eo.__eo_list_minclude xf xa xb = Eo.Term.Stuck := by
          rw [hcat]
          rcases hr with h | h
          · rw [hreqS _ _ h]; unfold Eo.__eo_list_minclude_rec; simp
          · rw [hreqS _ _ h]; unfold Eo.__eo_list_minclude_rec; split <;> simp_all
        rw [this]; exact hinv2.rep_stuck
      | some p =>
        obtain ⟨xsh, ysh, nilh⟩ := p
        obtain ⟨xs, ys, xr, hxs, hys, hnilh, hxl, hyl, hend, hn, hlx', hly'⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        step with multiset_inclusion_spec (alloc.vec.Vec.deref xsh) (alloc.vec.Vec.deref ysh)
          (by simp [alloc.vec.Vec.deref, Slice.length]; omega) h64 as ⟨foreign, contained, hfor, hcon⟩
        simp only [Bool.false_eq_true, ite_false]
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hnx : ∀ y ∈ xs, y ≠ Eo.Term.Stuck := eoList_valid_elems xs (hxl ▸ hva)
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hyl ▸ hvb)
        have hcm : contained = minclL xs ys := by
          have h := eraseAll_rep hinv2 (by simpa [alloc.vec.Vec.deref] using hxs)
            (by simpa [alloc.vec.Vec.deref] using hys)
          rw [hcon]
          simp only [alloc.vec.Vec.deref] at h ⊢
          cases hm : minclL xs ys
          · apply decide_eq_false; intro e; have := h.mp (by simpa using e); simp_all
          · simpa using h.mpr hm
        have hval : Eo.__eo_list_minclude xf xa xb = Eo.Term.Boolean (minclL xs ys) := by
          have hlx : Eo.__eo_is_list xf xa = Eo.Term.Boolean true := by
            rw [hxl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hend]; simp [hn]
          have hly : Eo.__eo_is_list xf xb = Eo.Term.Boolean true := by
            rw [hyl, is_list_eoList ys hxf (by rw [← hyl]; exact hxb) hend]; simp [hn]
          have hreqT : ∀ y, Eo.__eo_requires (Eo.Term.Boolean true) (Eo.Term.Boolean true) y = y := by
            intro y; simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
          rw [hcat, hlx, hly, hreqT, hreqT, hxl, hyl,
            get_elements_rec_eoList hxf (is_list_nil_not_apply hn) hxr,
            get_elements_rec_eoList hxf (is_list_nil_not_apply hn) hxr,
            minclude_rec_eoList ys xs hnx hny]
        unfold Store.boolean
        apply WP.dspec_mono (Store.literal_boolean_spec s2 contained hinv2 h64)
        rintro ⟨r3, s3⟩ ⟨hinv3, hg3, hr3⟩
        refine ⟨hinv3, hg2.trans hg3, ?_⟩
        cases r3 with
        | Err e => trivial
        | Ok t => simp only at hr3 ⊢; rw [hval, ← hcm]; exact hr3


/-- A handle of `xs` that is none of `ys`: a term of `xs` that is none of
theirs. -/
theorem foreign_rep {s : Store} (hinv : s.Inv) {ysh : List Term} {ys : List Eo.Term}
    (hy : List.Forall₂ s.Rep ysh ys) :
    ∀ {xsh : List Term} {xs : List Eo.Term}, List.Forall₂ s.Rep xsh xs →
      ((∃ x ∈ xsh, x ∉ ysh) ↔ (∃ x ∈ xs, x ∉ ys))
  | _, _, .nil => by simp
  | _, _, .cons (a := x) (b := τ) h hs => by
    have hm := rep_mem_iff hinv h hy
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [foreign_rep hinv hy hs, hm]

/-- Two lists of `f` that are one term have the same elements and nil. -/
theorem eoList_inj2 {xf r r' : Eo.Term} (hr : ∀ a b, r ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b)
    (hr' : ∀ a b, r' ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) :
    ∀ l l' : List Eo.Term, eoList xf r l = eoList xf r' l' → l = l' ∧ r = r'
  | [], [] => fun h => ⟨rfl, h⟩
  | [], y :: l' => fun h => absurd h (hr _ _)
  | x :: l, [] => fun h => absurd h.symm (hr' _ _)
  | x :: l, y :: l' => fun h => by
    simp only [eoList, Eo.Term.Apply.injEq] at h
    obtain ⟨e, r⟩ := eoList_inj2 hr hr' l l' h.2
    exact ⟨by rw [h.1.2, e], r⟩

/-- `eo::list_meq` on handles of an operator with one nil and two lists:
logos's `__eo_list_meq`. -/
theorem Store.builtin_spec_list_meq (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xa xb : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xa) (hc : s.Rep c xb)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n)
    (hleft : NotLeftNested xf) (huniq : UniqueNil xf) :
    generated.part0.Store.builtin_list s kind.EvalOp.ListMeq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_meq xf xa xb)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.ListMeq 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  have hcat : ∀ y z, Eo.__eo_list_meq xf y z = Eo.__eo_and
      (Eo.__eo_list_minclude_rec
        (Eo.__eo_requires (Eo.__eo_is_list xf y) (Eo.Term.Boolean true) (Eo.__eo_get_elements_rec y))
        (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true) (Eo.__eo_get_elements_rec z))
        (Eo.Term.Boolean true))
      (Eo.__eo_list_minclude_rec
        (Eo.__eo_requires (Eo.__eo_is_list xf z) (Eo.Term.Boolean true) (Eo.__eo_get_elements_rec z))
        (Eo.__eo_requires (Eo.__eo_is_list xf y) (Eo.Term.Boolean true) (Eo.__eo_get_elements_rec y))
        (Eo.Term.Boolean true)) := fun _ _ => rfl
  have hreqS : ∀ c y, c ≠ Eo.Term.Boolean true →
      Eo.__eo_requires c (Eo.Term.Boolean true) y = Eo.Term.Stuck := by
    intro c y hc; simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hc]
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
      have : Eo.__eo_list_meq Eo.Term.Stuck xa xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_list_minclude_rec, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, Eo.__eo_is_list, Eo.__eo_and]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_meq xf Eo.Term.Stuck xb = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_list_minclude_rec, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, Eo.__eo_is_list, Eo.__eo_and]
      rw [this]; exact hinv.rep_stuck
    by_cases hxb : xb = Eo.Term.Stuck
    · subst hxb
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_list_meq xf xa Eo.Term.Stuck = Eo.Term.Stuck := by
        rw [hcat]; simp [Eo.__eo_list_minclude_rec, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, Eo.__eo_is_list, Eo.__eo_and]
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hxb, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
    simp only [h0, h1, h2, Std.bind_ok]
    unfold generated.part0.Store.list_inclusion
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
        have : Eo.__eo_list_meq xf xa xb = Eo.Term.Stuck := by
          rw [hcat]
          rcases hr with h | h
          · rw [hreqS _ _ h]; simp [Eo.__eo_list_minclude_rec, Eo.__eo_and]
          · rw [hreqS _ _ h]
            unfold Eo.__eo_and; split <;> simp_all [Eo.__eo_list_minclude_rec]
        rw [this]; exact hinv2.rep_stuck
      | some p =>
        obtain ⟨xsh, ysh, nilh⟩ := p
        obtain ⟨xs, ys, xr, hxs, hys, hnilh, hxl, hyl, hend, hn, hlx', hly'⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        step with multiset_inclusion_spec (alloc.vec.Vec.deref xsh) (alloc.vec.Vec.deref ysh)
          (by simp [alloc.vec.Vec.deref, Slice.length]; omega) h64 as ⟨foreign, contained, hfor, hcon⟩
        simp only [ite_true]
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hnx : ∀ y ∈ xs, y ≠ Eo.Term.Stuck := eoList_valid_elems xs (hxl ▸ hva)
        have hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck := eoList_valid_elems ys (hyl ▸ hvb)
        have hxs' : List.Forall₂ s2.Rep xsh.val xs := by simpa [alloc.vec.Vec.deref] using hxs
        have hys' : List.Forall₂ s2.Rep ysh.val ys := by simpa [alloc.vec.Vec.deref] using hys
        have hcm : contained = minclL xs ys := by
          have h := eraseAll_rep hinv2 hxs' hys'
          rw [hcon]
          simp only [alloc.vec.Vec.deref] at h ⊢
          cases hm : minclL xs ys
          · apply decide_eq_false; intro e; have := h.mp (by simpa using e); simp_all
          · simpa using h.mpr hm
        have hfm : foreign = decide (∃ x ∈ xs, x ∉ ys) := by
          rw [hfor]
          simp only [alloc.vec.Vec.deref]
          congr 1
          apply propext
          simpa using foreign_rep hinv2 hys' hxs'
        have hval : Eo.__eo_list_meq xf xa xb = Eo.Term.Boolean (minclL xs ys && minclL ys xs) := by
          have hlx : Eo.__eo_is_list xf xa = Eo.Term.Boolean true := by
            rw [hxl, is_list_eoList xs hxf (by rw [← hxl]; exact hxa) hend]; simp [hn]
          have hly : Eo.__eo_is_list xf xb = Eo.Term.Boolean true := by
            rw [hyl, is_list_eoList ys hxf (by rw [← hyl]; exact hxb) hend]; simp [hn]
          have hreqT : ∀ y, Eo.__eo_requires (Eo.Term.Boolean true) (Eo.Term.Boolean true) y = y := by
            intro y; simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
          rw [hcat, hlx, hly, hreqT, hreqT, hxl, hyl,
            get_elements_rec_eoList hxf (is_list_nil_not_apply hn) hxr,
            get_elements_rec_eoList hxf (is_list_nil_not_apply hn) hxr,
            minclude_rec_eoList ys xs hnx hny, minclude_rec_eoList xs ys hny hnx]
          simp [Eo.__eo_and, SmtEval.native_and]
        have hcnt := (minclL_iff xs ys)
        have hcnt' := (minclL_iff ys xs)
        have hbool : ∀ (b : Bool) (s3 : Store), s3.Inv → s.Grows s3 →
            b = (minclL xs ys && minclL ys xs) →
            Store.boolean s3 b ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
              match r with
              | core.result.Result.Ok t => s'.Rep t (Eo.__eo_list_meq xf xa xb)
              | core.result.Result.Err _ => True ⦄div := by
          intro b s3 hinv3 hg3 hb
          unfold Store.boolean
          apply WP.dspec_mono (Store.literal_boolean_spec s3 b hinv3 h64)
          rintro ⟨r4, s4⟩ ⟨hinv4, hg4, hr4⟩
          refine ⟨hinv4, hg3.trans hg4, ?_⟩
          cases r4 with
          | Err e => trivial
          | Ok t => simp only at hr4 ⊢; rw [hval, ← hb]; exact hr4
        by_cases hf : foreign = true
        · simp only [hf, ite_true]
          apply hbool false s2 hinv2 hg2
          rw [hfm] at hf
          obtain ⟨x, hx, hxy⟩ := of_decide_eq_true hf
          have : minclL ys xs = false := by
            cases h : minclL ys xs
            · rfl
            · have h1 := (hcnt'.mp h) x
              rw [List.count_eq_zero_of_not_mem hxy] at h1
              have h2 := List.count_pos_iff.mpr hx
              omega
          simp [this]
        · simp only [Bool.not_eq_true] at hf
          simp only [hf, Bool.false_eq_true, ite_false]
          have hfalse : ¬ ∃ x ∈ xs, x ∉ ys := by
            rw [hfm] at hf; exact of_decide_eq_false hf
          by_cases hcn : contained = true
          · simp only [hcn, ite_true]
            have hc' : minclL xs ys = true := by rw [← hcm]; exact hcn
            step with list_parts_spec n hnil s2 hinv2 h64 (hg2.rem hrem) (Represents.grows ha hg2)
              (Represents.grows hc hg2) hleft as ⟨r4, s4, hinv4, hg4, hr4⟩
            cases r4 with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from]
              exact ⟨hinv4, hg2.trans hg4⟩
            | Ok o4 =>
              cases o4 with
              | none =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, WP.dspec_ok,
                  WP.uncurry'_pair]
                exact ⟨hinv4, hg2.trans hg4, trivial⟩
              | some p4 =>
                obtain ⟨ys1, rest1⟩ := p4
                obtain ⟨ys2, yr2, hys1, -, hyl2, hend2, -, -⟩ := hr4
                simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
                obtain ⟨hyy, -⟩ := eoList_inj2 hend hend2 ys ys2 (hyl.symm.trans hyl2)
                subst hyy
                apply hbool _ s4 hinv4 (hg2.trans hg4)
                have hl1 : xsh.val.length = xs.length := hxs'.length_eq
                have hl2 : ys1.val.length = ys.length := hys1.length_eq
                have key : xs.length = ys.length ↔ minclL ys xs = true := by
                  rw [hcnt']
                  constructor
                  · intro hl; exact ((meq_iff xs ys).mp ⟨hfalse, hcnt.mp hc', hl⟩).2
                  · intro h; exact ((meq_iff xs ys).mpr ⟨hcnt.mp hc', h⟩).2.2
                rw [hc', Bool.true_and]
                cases hm : minclL ys xs
                · apply decide_eq_false
                  intro e
                  have : xs.length = ys.length := by
                    have := congrArg (·.val) e; simp [alloc.vec.Vec.len] at this; omega
                  have := key.mp this; simp_all
                · apply decide_eq_true
                  apply UScalar.eq_of_val_eq
                  have := key.mpr hm
                  simp [alloc.vec.Vec.len]; omega
          · simp only [Bool.not_eq_true] at hcn
            simp only [hcn, Bool.false_eq_true, ite_false]
            apply hbool false s2 hinv2 hg2
            have : minclL xs ys = false := by rw [← hcm]; exact hcn
            simp [this]

end pathos_compiled_checker
