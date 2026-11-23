module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame

/-!
# The stuck value of a type, and the values a store can hold

`HasStuck`: what a program gives when none of its cases applies. `Valid`:
the values that a store can hold, in the sense the lemma that a program
is logos's function needs (lemma C: no application of or to the stuck
term), and that a handle stands only for such values.

(That a handle stands for a value at all is `Represents.rep`, in
`Store/Sem.lean`, for every type of the embedding.)

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The value that a program gives when none of its cases applies, in the
types that have one. (A program to a type without one has a case for
every argument, and the value here is never used.) -/
class HasStuck (α : Type) where
  stuck : α

instance : HasStuck Eo.Term := ⟨Eo.Term.Stuck⟩
instance : HasStuck Eo.Proof := ⟨Eo.Proof.Stuck⟩
instance : HasStuck Bool := ⟨false⟩

/-! ## Values that a store can hold

logos's functions are defined on every value of their types, among them
terms that no store holds: an application of the stuck term, or to it.
`apply` never makes one. Where a function of logos and the generated code
differ only on such values, the proofs say so with `Valid`. -/

mutual
/-- No application in the tree is of the stuck tree or to it, in the
fields of its nodes too. -/
def TreeValid : Tree → Prop
  | Tree.apply a b => a ≠ Tree.stuck ∧ b ≠ Tree.stuck ∧ TreeValid a ∧ TreeValid b
  | Tree.node _ ts => TreesValid ts
  | _ => True
/-- `TreeValid` of each tree of a list. -/
def TreesValid : List Tree → Prop
  | [] => True
  | t :: ts => TreeValid t ∧ TreesValid ts
end

/-- No application in the term is of the stuck term or to it, in the
indices of its operators too (`UOp1`, …, which the encoding makes the fields
of a node). An index may be the stuck term itself: logos builds
`set.empty`/`seq.empty` of `__eo_typeof t`, the stuck term when `t` has no
type, and the store holds it as it is (a node's fields are not checked, as
an application's are, `TermData.Wf`). Defined through the encoding, so
that it is the same definition for every calculus. -/
def TermValid (x : Eo.Term) : Prop := TreeValid (Embedded.enc x)

theorem enc_eq_stuck_iff (x : Eo.Term) : Embedded.enc x = Tree.stuck ↔ x = Eo.Term.Stuck := by
  constructor
  · exact Embed.inv_Term_Stuck
  · rintro rfl; simp [Embed.embedded_enc_Term, Embed.enc_Term]

theorem TermValid.apply (f a : Eo.Term) :
    TermValid (Eo.Term.Apply f a) ↔
      f ≠ Eo.Term.Stuck ∧ a ≠ Eo.Term.Stuck ∧ TermValid f ∧ TermValid a := by
  unfold TermValid
  rw [show Embedded.enc (Eo.Term.Apply f a) = Tree.apply (Embedded.enc f) (Embedded.enc a) by
    simp [Embed.embedded_enc_Term, Embed.enc_Term]]
  simp only [TreeValid, ne_eq, enc_eq_stuck_iff]

/-- The values of a type that a store can hold. -/
class Valid (α : Type) where
  valid : α → Prop

instance : Valid Eo.Term := ⟨TermValid⟩
instance : Valid Eo.Proof := ⟨fun p => match p with | Eo.Proof.pf F => TermValid F | _ => True⟩
instance : Valid Eo.CStateObj := ⟨fun _ => True⟩
instance : Valid Eo.CState := ⟨fun _ => True⟩
instance : Valid Bool := ⟨fun _ => True⟩

/-! The other types of the checker's arguments: `Valid` is `True`. Lemma C
needs no more of them, because no case of a program over them tells apart
values that no store holds. Their cases match data constructors, compare
strings (`native_streq`) and pass values on. A term inside one of them
(a datatype's field types, a command's terms) is compared or applied only
as the argument of a program over terms, whose own lemma C takes it
`Valid` and whose body has that from the term's handle
(`Store.Rep.valid`). The bounds that a stored string or bit-vector keeps
(`emb`) stay in `Represents.rep`, where the bodies' proofs use them. -/

instance : Valid (List Nat) := ⟨fun _ => True⟩  -- strings, as code points
instance : Valid Nat := ⟨fun _ => True⟩
instance : Valid Eo.CArgList := ⟨fun _ => True⟩
instance : Valid Eo.CCmdList := ⟨fun _ => True⟩
instance : Valid Eo.CIndexList := ⟨fun _ => True⟩
instance : Valid Eo.CRule := ⟨fun _ => True⟩
instance : Valid Eo.Datatype := ⟨fun _ => True⟩
instance : Valid Eo.DatatypeCons := ⟨fun _ => True⟩
instance : Valid Eo.DatatypeDecl := ⟨fun _ => True⟩
instance : Valid Smtm.SmtType := ⟨fun _ => True⟩
instance : Valid Smtm.SmtDatatype := ⟨fun _ => True⟩
instance : Valid Smtm.SmtDatatypeCons := ⟨fun _ => True⟩
instance : Valid Smtm.SmtDatatypeDecl := ⟨fun _ => True⟩
-- commands: their cases match the command's constructor and pass its
-- terms and proofs on to programs over terms (lemma C closes with `True`,
-- checked on `$eo_invoke_cmd`)
instance : Valid Eo.CCmd := ⟨fun _ => True⟩
-- SMT terms: `$smtx_typeof`'s cases match their constructors and treat
-- `None` and applications as any other value, so they tell apart no
-- terms that a store cannot hold (lemma C closes with `True`, checked on
-- `$smtx_typeof`)
instance : Valid Smtm.SmtTerm := ⟨fun _ => True⟩

@[simp] theorem Valid.apply (f a : Eo.Term) :
    Valid.valid (Eo.Term.Apply f a) ↔
      f ≠ Eo.Term.Stuck ∧ a ≠ Eo.Term.Stuck ∧ Valid.valid f ∧ Valid.valid a := by
  exact TermValid.apply f a

@[simp] theorem Valid.pf (F : Eo.Term) : Valid.valid (Eo.Proof.pf F) ↔ Valid.valid F := Iff.rfl

/-- A tree that a handle unfolds to is valid: the store makes no
application of or to the stuck term (`TermData.Wf`). -/
theorem Holds.valid {s : Store} (hinv : s.Inv) {t : Nat} {tr : Tree}
    (h : Holds s.nodes.val t tr) : TreeValid tr := by
  refine Holds.rec (nodes := s.nodes.val)
    (motive_1 := fun _ tr _ => TreeValid tr)
    (motive_2 := fun _ trs _ => TreesValid trs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; simp [TreeValid]
  · intros; simp [TreeValid]
  · intros; simp [TreeValid]
  · intros; simp [TreeValid]
  · intro k f a xf xa hlt hd hf ha ihf iha
    have hwf := hinv.terms.data k hlt
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    refine ⟨?_, ?_, ihf, iha⟩
    · rintro rfl
      cases hf with | stuck _ _ hd' => exact h3 hd'
    · rintro rfl
      cases ha with | stuck _ _ hd' => exact h4 hd'
  · intro _ _ _ _ _ _ _ ih; simpa [TreeValid] using ih
  · simp [TreesValid]
  · intro _ _ _ _ _ _ ih1 ih2; exact ⟨ih1, ih2⟩

/-- A term that a handle stands for is one that a store can hold in the
sense of `Valid`: no application in it is of or to the stuck term. -/
theorem Store.Rep.valid' {s : Store} (hinv : s.Inv) {t : Term} {x : Eo.Term}
    (h : s.Rep t x) : TermValid x :=
  Holds.valid hinv h.1

theorem Store.Rep.valid {s : Store} (hinv : s.Inv) {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    Valid.valid x := Store.Rep.valid' hinv h

/-- The formula of a proof that a handle stands for is valid. -/
theorem Represents.valid_proof {s : Store} (hinv : s.Inv) {t : Term} {p : Eo.Proof}
    (h : Represents.rep s t p) : Valid.valid p := by
  cases p with
  | Stuck => trivial
  | pf F =>
    obtain ⟨hh, he⟩ := h
    simp only [Embed.embedded_enc_Proof, Embed.enc_Proof] at hh
    simp only [Embed.embedded_emb_Proof, Embed.emb_Proof] at he
    cases hh with
    | node _ _ v _ _ _ hl =>
      generalize v.val = l at hl
      cases hl with
      | cons f _ _ _ hf _ => exact Store.Rep.valid' (t := f) hinv ⟨hf, he⟩

end pathos_compiled_checker
