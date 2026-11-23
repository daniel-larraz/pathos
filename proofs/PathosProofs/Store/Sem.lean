module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Rep
public import PathosProofs.Store.New
public import PathosProofs.Store.Tree
public import MiniEmbed

/-!
# The store's operations, on the terms that handles stand for

The lemmas a proof about a generated program uses: what `is_stuck`,
`unapply`, `apply`, the construction of an operator and the comparison of
two handles say about logos's values. A handle stands for a value when it
unfolds to the value's tree and the value is one the store can hold
(`Rep`, in `Store/Rep.lean`); `Represents.rep` says it of a handle of a
store, for a value of any type of the embedding, `Store.Rep` of a term.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The calls that a store can still make: what `enter` and `tick` count
against its limit. Every round of a loop ticks, so a loop's rounds use it
up (the measure of the induction over a loop). -/
def Store.budget (s : Store) : Nat := s.limits.calls.val - s.calls.val

/-- The store `s'` has the terms of `s` under the same handles, the same
limits and the same depth of calls, and no more calls left to make. -/
structure Store.Grows (s s' : Store) : Prop where
  nodes : s.nodes.val <+: s'.nodes.val
  limits : s'.limits = s.limits
  depth : s'.depth = s.depth
  budget : s'.budget ≤ s.budget

theorem Store.budget_congr {s s' : Store} (hl : s'.limits = s.limits) (hc : s'.calls = s.calls) :
    s'.budget = s.budget := by
  unfold Store.budget; rw [hl, hc]

theorem Store.Grows.refl (s : Store) : s.Grows s := ⟨List.prefix_refl _, rfl, rfl, le_refl _⟩

theorem Store.Grows.trans {s s' s'' : Store} (h : s.Grows s') (h' : s'.Grows s'') :
    s.Grows s'' :=
  ⟨h.nodes.trans h'.nodes, by rw [h'.limits, h.limits], by rw [h'.depth, h.depth],
    le_trans h'.budget h.budget⟩

theorem Store.Extends.grows {s s' : Store} (h : s.Extends s') : s.Grows s' :=
  ⟨h.1, h.2.1, h.2.2.2.1, by unfold Store.budget; rw [h.2.1, h.2.2.1]⟩

theorem Store.Extends.programs {s s' : Store} (h : s.Extends s') :
    s'.caches.programs = s.caches.programs := h.2.2.2.2.2.1

/-- The handle `t` of the store `s` stands for the value `x`. The generated
theorems are stated with it, for a value of any type: Lean finds the type
from the program's signature. -/
abbrev Represents.rep {α : Type} [Embedded α] (s : Store) (t : Term) (x : α) : Prop :=
  pathos_compiled_checker.Rep s.nodes.val t.val x

/-- The same for a term. -/
abbrev Store.Rep (s : Store) (t : Term) (x : Eo.Term) : Prop := Represents.rep s t x

theorem Represents.grows {α : Type} [Embedded α] {s s' : Store} {t : Term} {x : α}
    (h : Represents.rep s t x) (hg : s.Grows s') : Represents.rep s' t x :=
  Rep.mono hg.nodes h

theorem Represents.congr {α : Type} [Embedded α] {s s' : Store} {t : Term} {x : α}
    (h : Represents.rep s t x) (hn : s'.nodes = s.nodes) : Represents.rep s' t x := by
  unfold Represents.rep; rw [hn]; exact h

theorem Represents.lt {α : Type} [Embedded α] {s : Store} {t : Term} {x : α}
    (h : Represents.rep s t x) : t.val < s.nodes.length := Rep.lt h

/-- Two handles are equal exactly when the values they stand for are. -/
theorem Represents.eq_iff {α : Type} [Embedded α] {s : Store} {t u : Term} {x y : α}
    (hinv : s.Inv) (ht : Represents.rep s t x) (hu : Represents.rep s u y) :
    t = u ↔ x = y := by
  constructor
  · intro h; subst h; exact Rep.functional ht hu
  · intro h; subst h
    have := Rep.injective hinv.table.nodup ht hu
    scalar_tac

theorem Store.Rep.grows {s s' : Store} {t : Term} {x : Eo.Term}
    (h : s.Rep t x) (hg : s.Grows s') : s'.Rep t x := Represents.grows h hg

theorem Store.Rep.lt {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    t.val < s.nodes.length := Represents.lt h

theorem Store.Rep.eq_iff {s : Store} {t u : Term} {x y : Eo.Term} (hinv : s.Inv)
    (ht : s.Rep t x) (hu : s.Rep u y) : t = u ↔ x = y := Represents.eq_iff hinv ht hu

/-- A handle stands for the stuck term exactly when its data is that of
the stuck term. -/
theorem Store.Rep.stuck_iff {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    (s.data t).isStuck = true ↔ x = Eo.Term.Stuck := by
  rw [TermData.isStuck_iff]
  unfold Store.data
  constructor
  · intro hd
    have he := Holds.functional h.1 (Holds.stuck t.val h.lt hd)
    exact Embed.inv_Term_Stuck he
  · intro hx
    subst hx
    have h1 := h.1
    simp only [Embed.embedded_enc_Term, Embed.enc_Term] at h1
    cases h1 with
    | stuck _ _ hd => exact hd

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
  obtain ⟨hh, he⟩ := h
  generalize hx : Embedded.enc x = tx at hh
  cases hh with
  | apply _ f a xf xa _ hd hf ha =>
    obtain ⟨x1, x2, rfl, rfl, rfl⟩ := Embed.inv_Term_Apply hx
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    left
    exact ⟨f, a, x1, x2, rfl, ⟨hf, he.1⟩, ⟨ha, he.2⟩, by simp [hd]⟩
  | stuck _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx
  | lit _ _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx
  | native _ _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx
  | userop _ _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx
  | node _ _ _ _ _ hd _ =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.embedded_enc_Term, Embed.enc_Term] at hx

/-- The first handle stands for the stuck term. -/
theorem Store.Inv.rep_stuck {s : Store} (hinv : s.Inv) : s.Rep 0#u32 Eo.Term.Stuck := by
  refine ⟨?_, by simp [Embed.embedded_emb_Term, Embed.emb_Term]⟩
  simp only [Embed.embedded_enc_Term, Embed.enc_Term]
  exact Holds.stuck 0 hinv.terms.nonempty hinv.terms.stuck0

/-- The two terms of an application that a handle stands for are not
stuck. -/
theorem Store.Rep.apply_ne_stuck {s : Store} {t : Term} {x y : Eo.Term} (hinv : s.Inv)
    (h : s.Rep t (Eo.Term.Apply x y)) : x ≠ Eo.Term.Stuck ∧ y ≠ Eo.Term.Stuck := by
  have h1 := h.1
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at h1
  cases h1 with
  | apply _ f a _ _ hlt hd hf ha =>
    have hwf := hinv.terms.data t.val hlt
    unfold Store.data at hwf
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    constructor
    · intro hx; subst hx
      simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hf
      cases hf with | stuck _ _ hd' => exact h3 hd'
    · intro hy; subst hy
      simp only [Embed.embedded_enc_Term, Embed.enc_Term] at ha
      cases ha with | stuck _ _ hd' => exact h4 hd'

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
    refine ⟨?_, by simp only [Embed.embedded_emb_Term, Embed.emb_Term]; exact ⟨hf.2, ha.2⟩⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    exact Holds.apply t.val f a _ _ hlt hres.2 (Holds.mono hext.grows.nodes hf.1)
      (Holds.mono hext.grows.nodes ha.1)

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
  apply WP.dspec_mono (Store.construct_data_spec s (uopCtor op) args hinv h64 (Or.inl (uopCtor_embedding op)))
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    simp only at hres ⊢
    obtain ⟨hlt, v, hv, hd⟩ := hres
    refine ⟨?_, by simp [Embed.embedded_emb_Term, Embed.emb_Term]⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    rw [← uopCtor_eq_uop]
    exact Holds.node t.val (uopCtor op) v [] hlt hd (by rw [hv, hargs]; exact HoldsList.nil)

end pathos_compiled_checker
