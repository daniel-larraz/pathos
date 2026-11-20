module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Store.Tree
public import PathosProofs.Store.Sem

/-!
# `construct` and `destruct` of a data constructor, over trees

Every constructor that the runtime stores as a node over its fields
(`Embedding::Data`: all but the stuck term, applications, object literals
and user operators) is built and taken apart the same way. Here once, for
all of them, in terms of `Holds`: what `construct` gives on handles of
some trees is a handle of the node over them, and `destruct` on a handle
of a tree finds the handles of its fields exactly when the tree is a node
of that constructor. Neither changes what an earlier handle unfolds to;
`destruct` does not change the store.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `construct` of a data constructor on handles of the trees `xs` gives a
handle of the node over them. -/
theorem Store.construct_holds (s : Store) (c : schema.Constructor) (args : Slice Term)
    (xs : List Tree) (hinv : s.Inv) (h64 : Platform64) (hemb : c.embedding = ok Embedding.Data)
    (hargs : HoldsList s.nodes.val args.val xs) :
    Store.construct s c args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Holds s'.nodes.val t.val (Tree.node c xs)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_data_spec s c args hinv h64 hemb)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    simp only at hres ⊢
    obtain ⟨hlt, v, hv, hd⟩ := hres
    exact Holds.node t.val c v xs hlt hd (by rw [hv]; exact HoldsList.mono hext.grows.nodes hargs)

/-- `destruct` of a data constructor on a handle of the tree `x`: the
handles of the fields of `x` if it is a node of that constructor, nothing
otherwise; the store is the same. -/
theorem Store.destruct_holds {s : Store} {t : Term} {x : Tree} (c : schema.Constructor)
    (hemb : c.embedding = ok Embedding.Data) (h : Holds s.nodes.val t.val x) :
    (∃ (v : alloc.vec.Vec Term) (xs : List Tree), x = Tree.node c xs ∧
      HoldsList s.nodes.val v.val xs ∧
      Store.destruct s c t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ xs, x ≠ Tree.node c xs) ∧
      Store.destruct s c t = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s c t hemb]
  have hlt := h.lt
  simp only [hlt, ite_true]
  unfold Store.data
  cases h with
  | node _ d v xs _ hd hl =>
    rw [hd]
    by_cases hdc : d = c
    · subst hdc
      left; exact ⟨v, xs, rfl, hl, by simp⟩
    · right
      refine ⟨fun ys he => ?_, by simp [hdc]⟩
      injection he with h1 _
      exact hdc h1
  | stuck _ _ hd => right; exact ⟨(fun _ he => by cases he), by simp [hd]⟩
  | lit _ _ _ hd => right; exact ⟨(fun _ he => by cases he), by simp [hd]⟩
  | native _ _ _ hd => right; exact ⟨(fun _ he => by cases he), by simp [hd]⟩
  | userop _ _ _ hd => right; exact ⟨(fun _ he => by cases he), by simp [hd]⟩
  | apply _ _ _ _ _ _ hd _ _ => right; exact ⟨(fun _ he => by cases he), by simp [hd]⟩

end pathos_compiled_checker
