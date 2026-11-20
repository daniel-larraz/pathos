module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Tree
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Embed
public import MiniEmbed

/-!
# Handles and logos's values, over trees

A handle stands for a value when it unfolds to the value's tree (`Holds`,
`Embed.enc_T`) and the value is one that the store can hold
(`Embed.emb_T`). This file proves, for terms and native Booleans, what
`Store/Sem.lean` and `Runtime/Ops.lean` prove of the old relation `Rep`:
equal handles are equal values, what `is_stuck` and `unapply` say, and the
specifications of `apply`, `construct` of an operator, the Boolean literal
and the native Boolean. Nothing uses it yet; the switch of
`Represents.rep` to it is the next step (docs/handoff-m32.md).

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The handle `t` stands for the term `x`. -/
def Store.HRep (s : Store) (t : Term) (x : Eo.Term) : Prop :=
  Holds s.nodes.val t.val (Embed.enc_Term x) ∧ Embed.emb_Term x

/-- The handle `t` is the native Boolean `b`. -/
def Store.HBool (s : Store) (t : Term) (b : Bool) : Prop :=
  Holds s.nodes.val t.val (Tree.encBool b) ∧ Tree.okBool b

theorem Store.HRep.lt {s : Store} {t : Term} {x : Eo.Term} (h : s.HRep t x) :
    t.val < s.nodes.length := h.1.lt

theorem Store.HRep.grows {s s' : Store} {t : Term} {x : Eo.Term} (h : s.HRep t x)
    (hg : s.Grows s') : s'.HRep t x :=
  ⟨Holds.mono hg.nodes h.1, h.2⟩

theorem Store.HRep.congr {s s' : Store} {t : Term} {x : Eo.Term} (h : s.HRep t x)
    (hn : s'.nodes = s.nodes) : s'.HRep t x := by
  unfold Store.HRep; rw [hn]; exact h

theorem Store.HBool.grows {s s' : Store} {t : Term} {b : Bool} (h : s.HBool t b)
    (hg : s.Grows s') : s'.HBool t b :=
  ⟨Holds.mono hg.nodes h.1, h.2⟩

theorem Store.HBool.congr {s s' : Store} {t : Term} {b : Bool} (h : s.HBool t b)
    (hn : s'.nodes = s.nodes) : s'.HBool t b := by
  unfold Store.HBool; rw [hn]; exact h

/-- Two handles are equal exactly when the terms they stand for are. -/
theorem Store.HRep.eq_iff {s : Store} {t u : Term} {x y : Eo.Term} (hinv : s.Inv)
    (ht : s.HRep t x) (hu : s.HRep u y) : t = u ↔ x = y := by
  constructor
  · intro h; subst h
    have he := Holds.functional ht.1 hu.1
    have h1 := Embed.dec_enc_Term x ht.2
    rw [he, Embed.dec_enc_Term y hu.2] at h1
    exact (Option.some.inj h1).symm
  · intro h; subst h
    have := Holds.injective hinv.table.nodup ht.1 hu.1
    exact u32_eq_of_val this

/-- A handle stands for the stuck term exactly when its data is that of
the stuck term. -/
theorem Store.HRep.stuck_iff {s : Store} {t : Term} {x : Eo.Term} (h : s.HRep t x) :
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
    simp only [Embed.enc_Term] at h1
    cases h1 with
    | stuck _ _ hd => exact hd

theorem Store.HRep.is_stuck {s : Store} {t : Term} {x : Eo.Term} (h : s.HRep t x) :
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
theorem Store.HRep.unapply {s : Store} {t : Term} {x : Eo.Term} (h : s.HRep t x) :
    (∃ f a x1 x2, x = Eo.Term.Apply x1 x2 ∧ s.HRep f x1 ∧ s.HRep a x2 ∧
        Store.unapply s t = ok (core.result.Result.Ok (some (f, a)))) ∨
    ((∀ x1 x2, x ≠ Eo.Term.Apply x1 x2) ∧
        Store.unapply s t = ok (core.result.Result.Ok none)) := by
  rw [Store.unapply_eq]
  simp only [h.lt, ite_true]
  unfold Store.data
  obtain ⟨hh, he⟩ := h
  generalize hx : Embed.enc_Term x = tx at hh
  cases hh with
  | apply _ f a xf xa _ hd hf ha =>
    obtain ⟨x1, x2, rfl, rfl, rfl⟩ := Embed.inv_Term_Apply hx
    simp only [Embed.emb_Term] at he
    left
    exact ⟨f, a, x1, x2, rfl, ⟨hf, he.1⟩, ⟨ha, he.2⟩, by simp [hd]⟩
  | stuck _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.enc_Term] at hx
  | lit _ _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.enc_Term] at hx
  | native _ _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.enc_Term] at hx
  | userop _ _ _ hd =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.enc_Term] at hx
  | node _ _ _ _ _ hd _ =>
    right
    refine ⟨fun x1 x2 h => ?_, by simp [hd]⟩
    subst h; simp [Embed.enc_Term] at hx

/-- The first handle stands for the stuck term. -/
theorem Store.Inv.hrep_stuck {s : Store} (hinv : s.Inv) : s.HRep 0#u32 Eo.Term.Stuck := by
  refine ⟨?_, by simp [Embed.emb_Term]⟩
  simp only [Embed.enc_Term]
  exact Holds.stuck 0 hinv.terms.nonempty hinv.terms.stuck0

/-- The two terms of an application that a handle stands for are not
stuck. -/
theorem Store.HRep.apply_ne_stuck {s : Store} {t : Term} {x y : Eo.Term} (hinv : s.Inv)
    (h : s.HRep t (Eo.Term.Apply x y)) : x ≠ Eo.Term.Stuck ∧ y ≠ Eo.Term.Stuck := by
  have h1 := h.1
  simp only [Embed.enc_Term] at h1
  cases h1 with
  | apply _ f a _ _ hlt hd hf ha =>
    have hwf := hinv.terms.data t.val hlt
    unfold Store.data at hwf
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    constructor
    · intro hx; subst hx
      simp only [Embed.enc_Term] at hf
      cases hf with | stuck _ _ hd' => exact h3 hd'
    · intro hy; subst hy
      simp only [Embed.enc_Term] at ha
      cases ha with | stuck _ _ hd' => exact h4 hd'

/-- `apply` on the handles of two terms that are not stuck gives a handle
of their application. -/
theorem Store.apply_hrep (s : Store) (f a : Term) (x y : Eo.Term) (hinv : s.Inv)
    (h64 : Platform64) (hf : s.HRep f x) (ha : s.HRep a y)
    (hx : x ≠ Eo.Term.Stuck) (hy : y ≠ Eo.Term.Stuck) :
    Store.apply s f a ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.HRep t (Eo.Term.Apply x y)
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
    refine ⟨?_, by simp only [Embed.emb_Term]; exact ⟨hf.2, ha.2⟩⟩
    simp only [Embed.enc_Term]
    exact Holds.apply t.val f a _ _ hlt hres.2 (Holds.mono hext.grows.nodes hf.1)
      (Holds.mono hext.grows.nodes ha.1)

theorem uopCtor_eq_uop (op : Eo.UserOp) : uopCtor op = Embed.uop op := by
  cases op <;> rfl

/-- Constructing an operator of the signature gives a handle of it. -/
theorem Store.construct_uop_hrep (s : Store) (op : Eo.UserOp) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s (uopCtor op) args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.HRep t (Eo.Term.UOp op)
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
    refine ⟨?_, by simp [Embed.emb_Term]⟩
    simp only [Embed.enc_Term]
    rw [← uopCtor_eq_uop]
    exact Holds.node t.val (uopCtor op) v [] hlt hd (by rw [hv, hargs]; exact HoldsList.nil)

/-- `literal` with a Boolean gives a handle of it. -/
theorem Store.literal_boolean_hrep (s : Store) (b : Bool) (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Boolean b) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.HRep t (Eo.Term.Boolean b)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.literal
  simp only [Std.bind_ok]
  apply WP.dspec_mono (Store.intern_inv s (TermData.Literal (lit.Lit.Boolean b)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, by simp [Embed.emb_Term]⟩
    simp only [Embed.enc_Term]
    exact Holds.lit t.val _ hres.1 hres.2

/-- `native_bool` gives a handle of the native Boolean. -/
theorem Store.native_bool_hbool (s : Store) (b : Bool) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_bool s b ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.HBool t b
      | core.result.Result.Err _ => True ⦄div := by
  unfold native.Store.native_bool Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Boolean b)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨Holds.native t.val _ hres.1 hres.2, trivial⟩

/-- A term that a handle stands for is one that a store can hold in the
sense of `Valid`: no application in it is of or to the stuck term. -/
theorem Store.HRep.valid {s : Store} (hinv : s.Inv) {t : Term} {x : Eo.Term}
    (h : s.HRep t x) : TermValid x := by
  obtain ⟨hh, he⟩ := h
  generalize hx : Embed.enc_Term x = tr at hh
  refine (Holds.rec (nodes := s.nodes.val)
    (motive_1 := fun _ tr _ => ∀ x : Eo.Term, Embed.enc_Term x = tr → Embed.emb_Term x →
      TermValid x)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hh) x hx he
  · intro _ _ _ x hx _; cases x <;> simp_all [Embed.enc_Term, TermValid]
  · intro _ _ _ _ x hx _; cases x <;> simp_all [Embed.enc_Term, TermValid]
  · intro _ _ _ _ x hx _; cases x <;> simp_all [Embed.enc_Term, TermValid]
  · intro _ _ _ _ x hx _; cases x <;> simp_all [Embed.enc_Term, TermValid]
  · intro k f a xf xa hlt hd hf ha ihf iha x hx he
    obtain ⟨x1, x2, rfl, rfl, rfl⟩ := Embed.inv_Term_Apply hx
    simp only [Embed.emb_Term] at he
    have hwf := hinv.terms.data k hlt
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    refine ⟨?_, ?_, ihf x1 rfl he.1, iha x2 rfl he.2⟩
    · intro h1; subst h1
      simp only [Embed.enc_Term] at hf
      cases hf with | stuck _ _ hd' => exact h3 hd'
    · intro h2; subst h2
      simp only [Embed.enc_Term] at ha
      cases ha with | stuck _ _ hd' => exact h4 hd'
  · intro _ _ _ _ _ _ _ _ x hx _; cases x <;> simp_all [Embed.enc_Term, TermValid]
  · trivial
  · intros; trivial

end pathos_compiled_checker
