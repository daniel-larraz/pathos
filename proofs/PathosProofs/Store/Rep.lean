module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Intern
public import PathosProofs.Store.Tree
public import MiniEmbed

/-!
# Handles and logos's values

`Rep nodes t x`: in a store whose terms are `nodes`, the handle `t` stands
for the value `x` of logos (a term, a proof, a state, a native Boolean, …):
it unfolds to the tree that the value is stored as (`Holds`,
`Embedded.enc`, generated in `MiniEmbed`), and the value is one that the
store can hold (`Embedded.emb`). With the store's invariant a handle
stands for at most one value and a value has at most one handle, so the
generated code, which chooses a case by comparing handles, compares
values.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The constructor of the checker for an operator of the signature. -/
@[reducible] def uopCtor : Eo.UserOp → schema.Constructor
  | Eo.UserOp.Int => schema.Constructor.eo_Int
  | Eo.UserOp.Real => schema.Constructor.eo_Real
  | Eo.UserOp.BitVec => schema.Constructor.eo_BitVec
  | Eo.UserOp.Char => schema.Constructor.eo_Char
  | Eo.UserOp.Seq => schema.Constructor.eo_Seq
  | Eo.UserOp.not => schema.Constructor.eo_not
  | Eo.UserOp.and => schema.Constructor.eo_and
  | Eo.UserOp.imp => schema.Constructor.eo__3d_3e
  | Eo.UserOp.eq => schema.Constructor.eo__3d

theorem uopCtor_eq_uop (op : Eo.UserOp) : uopCtor op = Embed.uop op := by
  cases op <;> rfl

/-- The handle `t` stands for the value `x`. -/
def Rep {α : Type} [Embedded α] (nodes : List TermData) (t : Nat) (x : α) : Prop :=
  Holds nodes t (Embedded.enc x) ∧ Embedded.emb x

theorem Rep.lt {α : Type} [Embedded α] {nodes : List TermData} {t : Nat} {x : α}
    (h : Rep nodes t x) : t < nodes.length := h.1.lt

/-- A handle stands for at most one value. -/
theorem Rep.functional {α : Type} [Embedded α] {nodes : List TermData} {t : Nat} {x y : α}
    (hx : Rep nodes t x) (hy : Rep nodes t y) : x = y :=
  Embedded.enc_inj hx.2 hy.2 (Holds.functional hx.1 hy.1)

/-- A value has at most one handle, in a store where no two handles have
the same data. -/
theorem Rep.injective {α : Type} [Embedded α] {nodes : List TermData} {t u : Nat} {x : α}
    (nodup : ∀ i j : Nat, i < nodes.length → j < nodes.length → nodes[i]! = nodes[j]! → i = j)
    (ht : Rep nodes t x) (hu : Rep nodes u x) : t = u :=
  Holds.injective nodup ht.1 hu.1

/-- Handles keep what they stand for when the store gets more terms. -/
theorem Rep.mono {α : Type} [Embedded α] {nodes nodes' : List TermData} {t : Nat} {x : α}
    (hpre : nodes <+: nodes') (h : Rep nodes t x) : Rep nodes' t x :=
  ⟨Holds.mono hpre h.1, h.2⟩

/-- The handles of a list stand for the terms of a list, one for one: the
arguments of a program. -/
abbrev RepList (nodes : List TermData) : List Term → List Eo.Term → Prop :=
  List.Forall₂ (fun a x => Rep nodes a.val x)

theorem RepList.mono {nodes nodes' : List TermData} {ts : List Term} {xs : List Eo.Term}
    (hpre : nodes <+: nodes') (h : RepList nodes ts xs) : RepList nodes' ts xs :=
  List.Forall₂.imp (fun _ _ h => Rep.mono hpre h) h

theorem RepList.functional {nodes : List TermData} {ts : List Term} {xs ys : List Eo.Term}
    (h : RepList nodes ts xs) (h' : RepList nodes ts ys) : xs = ys := by
  induction h generalizing ys with
  | nil => cases h'; rfl
  | cons h1 _ ih =>
    cases h' with
    | cons h1' h2' => rw [Rep.functional h1 h1', ih h2']

end pathos_compiled_checker
