module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Rep
public import PathosProofs.Store.New

/-!
# The store's operations, on the terms that handles stand for

The lemmas a proof about a generated program uses: what `is_stuck`,
`unapply`, `apply`, the construction of an operator and the comparison of
two handles say about logos's terms.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The store `s'` has the terms of `s` under the same handles, the same
limits and the same depth of calls. -/
structure Store.Grows (s s' : Store) : Prop where
  nodes : s.nodes.val <+: s'.nodes.val
  limits : s'.limits = s.limits
  depth : s'.depth = s.depth

theorem Store.Grows.refl (s : Store) : s.Grows s := ⟨List.prefix_refl _, rfl, rfl⟩

theorem Store.Grows.trans {s s' s'' : Store} (h : s.Grows s') (h' : s'.Grows s'') :
    s.Grows s'' :=
  ⟨h.nodes.trans h'.nodes, by rw [h'.limits, h.limits], by rw [h'.depth, h.depth]⟩

theorem Store.Extends.grows {s s' : Store} (h : s.Extends s') : s.Grows s' :=
  ⟨h.1, h.2.1, h.2.2.2.1⟩

theorem Store.Extends.programs {s s' : Store} (h : s.Extends s') :
    s'.caches.programs = s.caches.programs := h.2.2.2.2.2

/-- The handle `t` of the store `s` stands for the term `x`. -/
abbrev Store.Rep (s : Store) (t : Term) (x : Eo.Term) : Prop :=
  pathos_compiled_checker.Rep s.nodes.val t.val x

theorem Store.Rep.grows {s s' : Store} {t : Term} {x : Eo.Term}
    (h : s.Rep t x) (hg : s.Grows s') : s'.Rep t x :=
  Rep.mono hg.nodes h

theorem Store.Rep.lt {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    t.val < s.nodes.length := pathos_compiled_checker.Rep.lt h

/-- Two handles are equal exactly when the terms they stand for are. -/
theorem Store.Rep.eq_iff {s : Store} {t u : Term} {x y : Eo.Term} (hinv : s.Inv)
    (ht : s.Rep t x) (hu : s.Rep u y) : t = u ↔ x = y := by
  constructor
  · intro h; subst h; exact Rep.functional ht hu
  · intro h; subst h
    have := Rep.injective hinv.table.nodup ht hu
    scalar_tac

/-- A handle stands for the stuck term exactly when its data is that of
the stuck term. -/
theorem Store.Rep.stuck_iff {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    (s.data t).isStuck = true ↔ x = Eo.Term.Stuck := by
  rw [TermData.isStuck_iff]
  unfold Store.data
  cases h with
  | stuck _ _ hd => simp [hd]
  | uop _ _ _ _ hd _ => simp [hd]
  | apply _ _ _ _ _ _ hd _ _ => simp [hd]
  | boolean _ _ _ hd => simp [hd]

theorem Store.Rep.is_stuck {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    Store.is_stuck s t = ok (core.result.Result.Ok (decide (x = Eo.Term.Stuck))) := by
  rw [Store.is_stuck_eq]
  simp only [h.lt, ite_true]
  congr 2
  by_cases hx : x = Eo.Term.Stuck
  · simp [hx, h.stuck_iff.mpr hx]
  · have : (s.data t).isStuck = false := by
      cases hs : (s.data t).isStuck
      · rfl
      · exact absurd (h.stuck_iff.mp hs) hx
    simp [hx, this]

/-- `unapply` on a handle: the two handles of an application, which stand
for its two terms, and nothing for any other term. -/
theorem Store.Rep.unapply {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    (∃ f a x1 x2, x = Eo.Term.Apply x1 x2 ∧ s.Rep f x1 ∧ s.Rep a x2 ∧
        Store.unapply s t = ok (core.result.Result.Ok (some (f, a)))) ∨
    ((∀ x1 x2, x ≠ Eo.Term.Apply x1 x2) ∧
        Store.unapply s t = ok (core.result.Result.Ok none)) := by
  rw [Store.unapply_eq]
  simp only [h.lt, ite_true]
  unfold Store.data
  cases h with
  | stuck _ _ hd => right; simp [hd]
  | uop _ _ _ _ hd _ => right; simp [hd]
  | apply _ f a x1 x2 _ hd hf ha => left; exact ⟨f, a, x1, x2, rfl, hf, ha, by simp [hd]⟩
  | boolean _ _ _ hd => right; simp [hd]

/-- The first handle stands for the stuck term. -/
theorem Store.Inv.rep_stuck {s : Store} (hinv : s.Inv) : s.Rep 0#u32 Eo.Term.Stuck :=
  Rep.stuck 0 hinv.terms.nonempty hinv.terms.stuck0

/-- The two terms of an application that a handle stands for are not
stuck. -/
theorem Store.Rep.apply_ne_stuck {s : Store} {t : Term} {x y : Eo.Term} (hinv : s.Inv)
    (h : s.Rep t (Eo.Term.Apply x y)) : x ≠ Eo.Term.Stuck ∧ y ≠ Eo.Term.Stuck := by
  cases h with
  | apply _ f a _ _ hlt hd hf ha =>
    have hwf := hinv.terms.data t.val hlt
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    constructor
    · intro hx
      have := (Store.Rep.stuck_iff (s := s) (t := f) hf).mpr hx
      exact h3 ((TermData.isStuck_iff _).mp this)
    · intro hy
      have := (Store.Rep.stuck_iff (s := s) (t := a) ha).mpr hy
      exact h4 ((TermData.isStuck_iff _).mp this)

/-- `apply` on the handles of two terms that are not stuck gives a handle
of their application. -/
theorem Store.apply_rep (s : Store) (f a : Term) (x y : Eo.Term) (hinv : s.Inv)
    (h64 : Platform64) (hf : s.Rep f x) (ha : s.Rep a y)
    (hx : x ≠ Eo.Term.Stuck) (hy : y ≠ Eo.Term.Stuck) :
    Store.apply s f a ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Apply x y)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.apply_spec s f a hinv h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    simp only at hres ⊢
    obtain ⟨_, hlt, hres⟩ := hres
    have hfs : (s.data f).isStuck = false := by
      cases hs : (s.data f).isStuck
      · rfl
      · exact absurd (hf.stuck_iff.mp hs) hx
    have has : (s.data a).isStuck = false := by
      cases hs : (s.data a).isStuck
      · rfl
      · exact absurd (ha.stuck_iff.mp hs) hy
    simp only [hfs, has, Bool.false_eq_true, ite_false] at hres
    exact Rep.apply t.val f a x y hlt hres.2 (hf.grows hext.grows) (ha.grows hext.grows)

theorem uopCtor_embedding (op : Eo.UserOp) :
    (uopCtor op).embedding = ok Embedding.Data := by
  cases op <;> rfl

/-- Constructing an operator of the signature gives a handle of it. -/
theorem Store.construct_uop_spec (s : Store) (op : Eo.UserOp) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s (uopCtor op) args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.UOp op)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_data_spec s (uopCtor op) args hinv h64 (uopCtor_embedding op))
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    simp only at hres ⊢
    obtain ⟨hlt, v, hv, hd⟩ := hres
    exact Rep.uop t.val op v hlt hd (by rw [hv, hargs])

end pathos_compiled_checker
