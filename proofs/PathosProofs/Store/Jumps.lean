module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Store.Table

/-!
# The jump pointers over state lists

`Store::state_nth` (the runtime's lookup for `$eo_state_proven_nth`) keeps a
side table, `state_jumps`, indexed by handle. The entry `(d, j)` of a `cons`
node of a state list, once computed, is the node's depth (the number of
`cons` nodes from it to the end of its list; `0` means no entry) and a node
`j` that following tails from it reaches after between one and `d` steps.
That is the invariant here (`JumpsOK`), stated over the store's terms: the
nodes never change, so it holds as long as the table is only written by
`state_depth`, which keeps it.

A `cons` node is a node of the checker's `$emb_s.cons` with two fields,
which is what `state_tail` tests (the generated code passes that
constructor). Handles are naturals here.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The constructor of a non-empty state, whose lists `state_nth` walks. -/
abbrev stateCons : schema.Constructor := schema.Constructor.eo__24emb_5fs_2econs

/-- `t` is a `cons` node of a state list, with tail `u`. -/
def StateTail (nodes : List TermData) (t u : Nat) : Prop :=
  ∃ fields : alloc.vec.Vec Term, t < nodes.length ∧
    nodes[t]! = TermData.Node stateCons fields ∧ fields.val.length = 2 ∧
    (fields.val[1]!).val = u

/-- The depth of `t`: the number of `cons` nodes from it to the end of its
list (a handle of the store that is no `cons` node has depth 0). -/
inductive StateDepth (nodes : List TermData) : Nat → Nat → Prop
  | stop (t : Nat) : t < nodes.length → (∀ u, ¬ StateTail nodes t u) → StateDepth nodes t 0
  | step (t u d : Nat) : StateTail nodes t u → StateDepth nodes u d → StateDepth nodes t (d + 1)

/-- Following `k` tails from `t` reaches `v`. -/
inductive StateDown (nodes : List TermData) : Nat → Nat → Nat → Prop
  | zero (t : Nat) : StateDown nodes t 0 t
  | succ (t u k v : Nat) : StateTail nodes t u → StateDown nodes u k v →
      StateDown nodes t (k + 1) v

/-- What the entry `e` of the handle `t` says, where it is filled. -/
def JumpOK (nodes : List TermData) (t : Nat) (e : Std.U32 × Term) : Prop :=
  0 < e.1.val → StateDepth nodes t e.1.val ∧
    ∃ k, 1 ≤ k ∧ k ≤ e.1.val ∧ StateDown nodes t k e.2.val

/-- Every filled entry of the table of jump pointers is right. -/
def JumpsOK (nodes : List TermData) (jumps : List (Std.U32 × Term)) : Prop :=
  ∀ (t : Nat) (e : Std.U32 × Term), jumps[t]? = some e → JumpOK nodes t e

theorem StateTail.lt {nodes : List TermData} {t u : Nat} (h : StateTail nodes t u) :
    t < nodes.length := by
  obtain ⟨_, h, _⟩ := h; exact h

theorem StateTail.functional {nodes : List TermData} {t u u' : Nat}
    (h : StateTail nodes t u) (h' : StateTail nodes t u') : u = u' := by
  obtain ⟨f, _, hd, _, hu⟩ := h
  obtain ⟨f', _, hd', _, hu'⟩ := h'
  rw [hd] at hd'
  cases hd'
  rw [← hu, ← hu']

theorem StateTail.mono {nodes nodes' : List TermData} (hpre : nodes <+: nodes') {t u : Nat}
    (h : StateTail nodes t u) : StateTail nodes' t u := by
  obtain ⟨f, hlt, hd, hl, hu⟩ := h
  obtain ⟨rest, rfl⟩ := hpre
  refine ⟨f, by simp; omega, ?_, hl, hu⟩
  rw [getElem!_append_left _ _ _ hlt]; exact hd

/-- In a longer list of terms, a handle of the shorter one has the same tail. -/
theorem StateTail.of_mono {nodes nodes' : List TermData} (hpre : nodes <+: nodes') {t u : Nat}
    (ht : t < nodes.length) (h : StateTail nodes' t u) : StateTail nodes t u := by
  obtain ⟨f, _, hd, hl, hu⟩ := h
  obtain ⟨rest, rfl⟩ := hpre
  refine ⟨f, ht, ?_, hl, hu⟩
  rw [getElem!_append_left _ _ _ ht] at hd; exact hd

theorem StateDepth.lt {nodes : List TermData} {t d : Nat} (h : StateDepth nodes t d) :
    t < nodes.length := by
  cases h with
  | stop _ h _ => exact h
  | step _ _ _ h _ => exact h.lt

theorem StateDepth.mono {nodes nodes' : List TermData} (hpre : nodes <+: nodes') {t d : Nat}
    (h : StateDepth nodes t d) : StateDepth nodes' t d := by
  induction h with
  | stop t ht hno =>
    refine StateDepth.stop t (by obtain ⟨r, rfl⟩ := hpre; simp; omega) ?_
    intro u hu; exact hno u (hu.of_mono hpre ht)
  | step t u d htl _ ih => exact StateDepth.step t u d (htl.mono hpre) ih

theorem StateDepth.functional {nodes : List TermData} {t d d' : Nat}
    (h : StateDepth nodes t d) (h' : StateDepth nodes t d') : d = d' := by
  induction h generalizing d' with
  | stop t _ hno =>
    cases h' with
    | stop => rfl
    | step _ u _ htl _ => exact absurd htl (hno u)
  | step t u d htl _ ih =>
    cases h' with
    | stop _ _ hno => exact absurd htl (hno u)
    | step _ u' d'' htl' hd' =>
      rw [htl.functional htl'] at ih
      rw [ih hd']

theorem StateDown.mono {nodes nodes' : List TermData} (hpre : nodes <+: nodes') {t k v : Nat}
    (h : StateDown nodes t k v) : StateDown nodes' t k v := by
  induction h with
  | zero t => exact StateDown.zero t
  | succ t u k v htl _ ih => exact StateDown.succ t u k v (htl.mono hpre) ih

theorem StateDown.trans {nodes : List TermData} {t k u l v : Nat}
    (h : StateDown nodes t k u) (h' : StateDown nodes u l v) : StateDown nodes t (k + l) v := by
  induction h with
  | zero t => simpa using h'
  | succ t w k u htl _ ih =>
    rw [show k + 1 + l = (k + l) + 1 by omega]
    exact StateDown.succ _ _ _ _ htl (ih h')

/-- Going down `k ≤ d` tails from a node of depth `d` reaches one of depth
`d - k`. -/
theorem StateDepth.down {nodes : List TermData} {t d k v : Nat} (h : StateDepth nodes t d)
    (hk : StateDown nodes t k v) (hle : k ≤ d) : StateDepth nodes v (d - k) := by
  induction hk generalizing d with
  | zero t => simpa using h
  | succ t u k v htl _ ih =>
    cases h with
    | stop _ _ hno => exact absurd htl (hno u)
    | step _ u' d' htl' hd' =>
      rw [htl.functional htl'] at ih
      have := ih hd' (by omega)
      rwa [show d' + 1 - (k + 1) = d' - k by omega]

theorem JumpsOK.mono {nodes nodes' : List TermData} {jumps : List (Std.U32 × Term)}
    (hpre : nodes <+: nodes') (h : JumpsOK nodes jumps) : JumpsOK nodes' jumps := by
  intro t e he hpos
  obtain ⟨hd, k, h1, h2, hk⟩ := h t e he hpos
  exact ⟨hd.mono hpre, k, h1, h2, hk.mono hpre⟩

/-- The table of a new store, which is empty. -/
theorem JumpsOK.nil (nodes : List TermData) : JumpsOK nodes [] := by
  intro t e he; simp at he

end pathos_compiled_checker
