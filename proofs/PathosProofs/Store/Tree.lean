module
public import MiniChecker
public import PathosProofs.Util

/-!
# What a handle unfolds to

**Work in progress: this file does not compile yet and nothing imports it.**
See docs/handoff-m32.md.

A handle of the store names data that names other handles. Unfolded all
the way it is a tree, `Tree`, and `Holds nodes t x` says that the handle
`t` unfolds to the tree `x` in a store whose terms are `nodes`.

Every value of logos that the checker computes with (a term, a proof, a
state, a native number) is embedded in the store, and how is a function
from the value to its tree (`enc`, generated for each type with the
checker). That a handle stands for a value is then one relation for all
types: the handle unfolds to the value's tree. What is proved here once
holds for all of them: a handle unfolds to at most one tree, a tree has at
most one handle in a store without duplicates, and both survive the store
growing.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The data of a handle with the handles in it unfolded. -/
inductive Tree : Type where
  | stuck : Tree
  | lit : lit.Lit → Tree
  | native : lit.Lit → Tree
  | userop : schema.Constructor → Tree
  | apply : Tree → Tree → Tree
  | node : schema.Constructor → List Tree → Tree

mutual
/-- The handle `t` unfolds to the tree `x`. -/
inductive Holds (nodes : List TermData) : Nat → Tree → Prop where
  | stuck (t : Nat) : t < nodes.length → nodes[t]! = TermData.Stuck → Holds nodes t Tree.stuck
  | lit (t : Nat) (l : lit.Lit) :
      t < nodes.length → nodes[t]! = TermData.Literal l → Holds nodes t (Tree.lit l)
  | native (t : Nat) (l : lit.Lit) :
      t < nodes.length → nodes[t]! = TermData.Native l → Holds nodes t (Tree.native l)
  | userop (t : Nat) (c : schema.Constructor) :
      t < nodes.length → nodes[t]! = TermData.UserOp c → Holds nodes t (Tree.userop c)
  | apply (t : Nat) (f a : Term) (x y : Tree) :
      t < nodes.length → nodes[t]! = TermData.Apply f a →
      Holds nodes f.val x → Holds nodes a.val y → Holds nodes t (Tree.apply x y)
  | node (t : Nat) (c : schema.Constructor) (v : alloc.vec.Vec Term) (xs : List Tree) :
      t < nodes.length → nodes[t]! = TermData.Node c v →
      HoldsList nodes v.val xs → Holds nodes t (Tree.node c xs)
/-- The handles of a list unfold to the trees of a list, one for one. -/
inductive HoldsList (nodes : List TermData) : List Term → List Tree → Prop where
  | nil : HoldsList nodes [] []
  | cons (h : Term) (hs : List Term) (x : Tree) (xs : List Tree) :
      Holds nodes h.val x → HoldsList nodes hs xs → HoldsList nodes (h :: hs) (x :: xs)
end

theorem Holds.lt {nodes : List TermData} {t : Nat} {x : Tree} (h : Holds nodes t x) :
    t < nodes.length := by
  cases h <;> assumption

theorem HoldsList.length {nodes : List TermData} {hs : List Term} {xs : List Tree}
    (h : HoldsList nodes hs xs) : hs.length = xs.length := by
  induction hs generalizing xs with
  | nil => cases h; rfl
  | cons a l ih => cases h with | cons _ _ _ _ _ h2 => simp [ih h2]

/-- A handle unfolds to at most one tree. -/
theorem Holds.functional {nodes : List TermData} {t : Nat} {x y : Tree}
    (hx : Holds nodes t x) (hy : Holds nodes t y) : x = y := by
  refine Holds.rec (nodes := nodes)
    (motive_1 := fun t x _ => ∀ y, Holds nodes t y → x = y)
    (motive_2 := fun hs xs _ => ∀ ys, HoldsList nodes hs ys → xs = ys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx y hy
  · intro t _ hd y hy; cases hy <;> simp_all
  · intro t l _ hd y hy; cases hy <;> simp_all
  · intro t l _ hd y hy; cases hy <;> simp_all
  · intro t c _ hd y hy; cases hy <;> simp_all
  · intro t f a x1 y1 _ hd _ _ ihf iha y hy
    cases hy with
    | apply _ f' a' x2 y2 _ hd' hf' ha' =>
      rw [hd] at hd'
      injection hd' with h1 h2
      subst h1; subst h2
      rw [ihf _ hf', iha _ ha']
    | _ => simp_all
  · intro t c v xs _ hd _ ih y hy
    cases hy with
    | node _ c' v' xs' _ hd' hl' =>
      rw [hd] at hd'
      injection hd' with h1 h2
      subst h1; subst h2
      rw [ih _ hl']
    | _ => simp_all
  · intro ys hl; cases hl; rfl
  · intro h hs x xs _ _ ih1 ih2 ys hl
    cases hl with
    | cons _ _ y ys' h1 h2 => rw [ih1 _ h1, ih2 _ h2]

theorem HoldsList.functional {nodes : List TermData} {hs : List Term} {xs ys : List Tree}
    (h : HoldsList nodes hs xs) (h' : HoldsList nodes hs ys) : xs = ys := by
  induction hs generalizing xs ys with
  | nil => cases h; cases h'; rfl
  | cons a l ih =>
    cases h with
    | cons _ _ _ _ h1 h2 =>
      cases h' with
      | cons _ _ _ _ h1' h2' => rw [Holds.functional h1 h1', ih h2 h2']

/-- A tree has at most one handle, in a store where no two handles have the
same data. -/
theorem Holds.injective {nodes : List TermData} {t u : Nat} {x : Tree}
    (nodup : ∀ i j : Nat, i < nodes.length → j < nodes.length → nodes[i]! = nodes[j]! → i = j)
    (ht : Holds nodes t x) (hu : Holds nodes u x) : t = u := by
  refine Holds.rec (nodes := nodes)
    (motive_1 := fun t x _ => ∀ u, Holds nodes u x → t = u)
    (motive_2 := fun hs xs _ => ∀ hs', HoldsList nodes hs' xs → hs = hs')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht u hu
  · intro t hlt hd u hu
    cases hu with | stuck _ hlt' hd' => exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  · intro t l hlt hd u hu
    cases hu with | lit _ _ hlt' hd' => exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  · intro t l hlt hd u hu
    cases hu with | native _ _ hlt' hd' => exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  · intro t c hlt hd u hu
    cases hu with | userop _ _ hlt' hd' => exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  · intro t f a x1 y1 hlt hd _ _ ihf iha u hu
    cases hu with
    | apply _ f' a' _ _ hlt' hd' hf' ha' =>
      have h1 : f = f' := by have := ihf _ hf'; scalar_tac
      have h2 : a = a' := by have := iha _ ha'; scalar_tac
      subst h1; subst h2
      exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  · intro t c v xs hlt hd _ ih u hu
    cases hu with
    | node _ _ v' _ hlt' hd' hl' =>
      have hv : v = v' := alloc.vec.Vec.ext _ _ (ih _ hl')
      subst hv
      exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  · intro hs' hl; cases hl; rfl
  · intro h hs x xs _ _ ih1 ih2 hs' hl
    cases hl with
    | cons h' hs'' _ _ h1 h2 =>
      have e1 : h = h' := by have := ih1 _ h1; scalar_tac
      rw [e1, ih2 _ h2]

/-- Handles keep what they unfold to when the store gets more terms. -/
theorem Holds.mono {nodes nodes' : List TermData} {t : Nat} {x : Tree}
    (hpre : nodes <+: nodes') (h : Holds nodes t x) : Holds nodes' t x := by
  have hlen := hpre.length_le
  have hget : ∀ i : Nat, i < nodes.length → nodes'[i]! = nodes[i]! := by
    intro i hi
    obtain ⟨r, rfl⟩ := hpre
    exact getElem!_append_left _ _ _ hi
  refine Holds.rec (nodes := nodes)
    (motive_1 := fun t x _ => Holds nodes' t x)
    (motive_2 := fun hs xs _ => HoldsList nodes' hs xs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro t hlt hd; exact Holds.stuck t (by omega) (by rw [hget t hlt]; exact hd)
  · intro t l hlt hd; exact Holds.lit t l (by omega) (by rw [hget t hlt]; exact hd)
  · intro t l hlt hd; exact Holds.native t l (by omega) (by rw [hget t hlt]; exact hd)
  · intro t c hlt hd; exact Holds.userop t c (by omega) (by rw [hget t hlt]; exact hd)
  · intro t f a x y hlt hd _ _ ihf iha
    exact Holds.apply t f a x y (by omega) (by rw [hget t hlt]; exact hd) ihf iha
  · intro t c v xs hlt hd _ ih
    exact Holds.node t c v xs (by omega) (by rw [hget t hlt]; exact hd) ih
  · exact HoldsList.nil
  · intro h hs x xs _ _ ih1 ih2; exact HoldsList.cons h hs x xs ih1 ih2

theorem HoldsList.mono {nodes nodes' : List TermData} {hs : List Term} {xs : List Tree}
    (hpre : nodes <+: nodes') (h : HoldsList nodes hs xs) : HoldsList nodes' hs xs := by
  induction hs generalizing xs with
  | nil => cases h; exact HoldsList.nil
  | cons a l ih =>
    cases h with
    | cons _ _ x xs' h1 h2 => exact HoldsList.cons a l x xs' (Holds.mono hpre h1) (ih h2)

end pathos_compiled_checker
