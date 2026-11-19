module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Ops

/-!
# Handles and logos's terms

`Rep nodes t x`: in a store whose terms are `nodes`, the handle `t` stands
for logos's term `x` (CpcMini's `Eo.Term`). With the store's invariant a
handle stands for at most one term and a term has at most one handle, so
the generated code, which chooses a case by comparing handles, compares
terms.

The relation covers the terms that the pilot's programs meet: the stuck
term, the operators of the signature, applications and Booleans. The
other constructors of `Eo.Term` (numerals, strings, variables, datatypes)
are embedded the same way, as literals or as nodes with their fields, and
are not written out yet.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The constructor of the checker for an operator of the signature. -/
def uopCtor : Eo.UserOp → schema.Constructor
  | Eo.UserOp.Int => schema.Constructor.eo_Int
  | Eo.UserOp.Real => schema.Constructor.eo_Real
  | Eo.UserOp.BitVec => schema.Constructor.eo_BitVec
  | Eo.UserOp.Char => schema.Constructor.eo_Char
  | Eo.UserOp.Seq => schema.Constructor.eo_Seq
  | Eo.UserOp.not => schema.Constructor.eo_not
  | Eo.UserOp.and => schema.Constructor.eo_and
  | Eo.UserOp.imp => schema.Constructor.eo__3d_3e
  | Eo.UserOp.eq => schema.Constructor.eo__3d

theorem uopCtor_inj {a b : Eo.UserOp} (h : uopCtor a = uopCtor b) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [uopCtor] at h)

/-- The handle `t` stands for the term `x`. -/
inductive Rep (nodes : List TermData) : Nat → Eo.Term → Prop where
  | stuck (t : Nat) : t < nodes.length → nodes[t]! = TermData.Stuck → Rep nodes t Eo.Term.Stuck
  | uop (t : Nat) (op : Eo.UserOp) (v : alloc.vec.Vec Term) :
      t < nodes.length → nodes[t]! = TermData.Node (uopCtor op) v → v.val = [] →
      Rep nodes t (Eo.Term.UOp op)
  | apply (t : Nat) (f a : Term) (x y : Eo.Term) :
      t < nodes.length → nodes[t]! = TermData.Apply f a →
      Rep nodes f.val x → Rep nodes a.val y → Rep nodes t (Eo.Term.Apply x y)
  | boolean (t : Nat) (b : Bool) :
      t < nodes.length → nodes[t]! = TermData.Literal (lit.Lit.Boolean b) →
      Rep nodes t (Eo.Term.Boolean b)

theorem Rep.lt {nodes : List TermData} {t : Nat} {x : Eo.Term} (h : Rep nodes t x) :
    t < nodes.length := by
  cases h <;> assumption

/-- A handle stands for at most one term. -/
theorem Rep.functional {nodes : List TermData} {t : Nat} {x y : Eo.Term}
    (hx : Rep nodes t x) (hy : Rep nodes t y) : x = y := by
  induction hx generalizing y with
  | stuck t _ hd =>
    cases hy with
    | stuck => rfl
    | uop _ _ _ _ hd' _ => rw [hd] at hd'; cases hd'
    | apply _ _ _ _ _ _ hd' _ _ => rw [hd] at hd'; cases hd'
    | boolean _ _ _ hd' => rw [hd] at hd'; cases hd'
  | uop t op v _ hd hv =>
    cases hy with
    | stuck _ _ hd' => rw [hd] at hd'; cases hd'
    | uop _ op' v' _ hd' _ =>
      rw [hd] at hd'
      injection hd' with h1 h2
      rw [uopCtor_inj h1]
    | apply _ _ _ _ _ _ hd' _ _ => rw [hd] at hd'; cases hd'
    | boolean _ _ _ hd' => rw [hd] at hd'; cases hd'
  | apply t f a x1 y1 _ hd _ _ ihf iha =>
    cases hy with
    | stuck _ _ hd' => rw [hd] at hd'; cases hd'
    | uop _ _ _ _ hd' _ => rw [hd] at hd'; cases hd'
    | apply _ f' a' x2 y2 _ hd' hf' ha' =>
      rw [hd] at hd'
      injection hd' with h1 h2
      subst h1; subst h2
      rw [ihf hf', iha ha']
    | boolean _ _ _ hd' => rw [hd] at hd'; cases hd'
  | boolean t b _ hd =>
    cases hy with
    | stuck _ _ hd' => rw [hd] at hd'; cases hd'
    | uop _ _ _ _ hd' _ => rw [hd] at hd'; cases hd'
    | apply _ _ _ _ _ _ hd' _ _ => rw [hd] at hd'; cases hd'
    | boolean _ b' _ hd' =>
      rw [hd] at hd'
      injection hd' with h1
      injection h1 with h2
      rw [h2]

/-- A term has at most one handle, in a store where no two handles have
the same data. -/
theorem Rep.injective {nodes : List TermData} {t u : Nat} {x : Eo.Term}
    (nodup : ∀ i j : Nat, i < nodes.length → j < nodes.length → nodes[i]! = nodes[j]! → i = j)
    (ht : Rep nodes t x) (hu : Rep nodes u x) : t = u := by
  induction ht generalizing u with
  | stuck t hlt hd =>
    cases hu with
    | stuck _ hlt' hd' => exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  | uop t op v hlt hd hv =>
    cases hu with
    | uop _ _ v' hlt' hd' hv' =>
      have : v = v' := alloc.vec.Vec.ext _ _ (by rw [hv, hv'])
      subst this
      exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  | apply t f a x1 y1 hlt hd _ _ ihf iha =>
    cases hu with
    | apply _ f' a' _ _ hlt' hd' hf' ha' =>
      have h1 : f = f' := by have := ihf hf'; scalar_tac
      have h2 : a = a' := by have := iha ha'; scalar_tac
      subst h1; subst h2
      exact nodup _ _ hlt hlt' (by rw [hd, hd'])
  | boolean t b hlt hd =>
    cases hu with
    | boolean _ _ hlt' hd' => exact nodup _ _ hlt hlt' (by rw [hd, hd'])

/-- Handles keep what they stand for when the store gets more terms. -/
theorem Rep.mono {nodes nodes' : List TermData} {t : Nat} {x : Eo.Term}
    (hpre : nodes <+: nodes') (h : Rep nodes t x) : Rep nodes' t x := by
  have hlen := hpre.length_le
  have hget : ∀ i : Nat, i < nodes.length → nodes'[i]! = nodes[i]! := by
    intro i hi
    obtain ⟨r, rfl⟩ := hpre
    exact getElem!_append_left _ _ _ hi
  induction h with
  | stuck t hlt hd => exact Rep.stuck t (by omega) (by rw [hget t hlt]; exact hd)
  | uop t op v hlt hd hv => exact Rep.uop t op v (by omega) (by rw [hget t hlt]; exact hd) hv
  | apply t f a x y hlt hd _ _ ihf iha =>
    exact Rep.apply t f a x y (by omega) (by rw [hget t hlt]; exact hd) ihf iha
  | boolean t b hlt hd => exact Rep.boolean t b (by omega) (by rw [hget t hlt]; exact hd)

end pathos_compiled_checker
