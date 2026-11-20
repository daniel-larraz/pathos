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

/-- No application in the term is of the stuck term or to it. -/
def TermValid : Eo.Term → Prop
  | Eo.Term.Apply f a => f ≠ Eo.Term.Stuck ∧ a ≠ Eo.Term.Stuck ∧ TermValid f ∧ TermValid a
  | _ => True

/-- The values of a type that a store can hold. -/
class Valid (α : Type) where
  valid : α → Prop

instance : Valid Eo.Term := ⟨TermValid⟩
instance : Valid Eo.Proof := ⟨fun p => match p with | Eo.Proof.pf F => TermValid F | _ => True⟩
instance : Valid Eo.CStateObj := ⟨fun _ => True⟩
instance : Valid Eo.CState := ⟨fun _ => True⟩
instance : Valid Bool := ⟨fun _ => True⟩

@[simp] theorem Valid.apply (f a : Eo.Term) :
    Valid.valid (Eo.Term.Apply f a) ↔
      f ≠ Eo.Term.Stuck ∧ a ≠ Eo.Term.Stuck ∧ Valid.valid f ∧ Valid.valid a := by
  show TermValid _ ↔ _ ∧ _ ∧ TermValid _ ∧ TermValid _
  simp [TermValid]

@[simp] theorem Valid.pf (F : Eo.Term) : Valid.valid (Eo.Proof.pf F) ↔ Valid.valid F := Iff.rfl

/-- A term that a handle stands for is one that a store can hold in the
sense of `Valid`: no application in it is of or to the stuck term. -/
theorem Store.Rep.valid' {s : Store} (hinv : s.Inv) {t : Term} {x : Eo.Term}
    (h : s.Rep t x) : TermValid x := by
  obtain ⟨hh, he⟩ := h
  generalize hx : Embedded.enc x = tr at hh
  refine (Holds.rec (nodes := s.nodes.val)
    (motive_1 := fun _ tr _ => ∀ x : Eo.Term, Embedded.enc x = tr → Embedded.emb x →
      TermValid x)
    (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hh) x hx he
  · intro _ _ _ x hx _; cases x <;> simp_all [Embed.embedded_enc_Term, Embed.enc_Term, TermValid]
  · intro _ _ _ _ x hx _; cases x <;> simp_all [Embed.embedded_enc_Term, Embed.enc_Term, TermValid]
  · intro _ _ _ _ x hx _; cases x <;> simp_all [Embed.embedded_enc_Term, Embed.enc_Term, TermValid]
  · intro _ _ _ _ x hx _; cases x <;> simp_all [Embed.embedded_enc_Term, Embed.enc_Term, TermValid]
  · intro k f a xf xa hlt hd hf ha ihf iha x hx he
    obtain ⟨x1, x2, rfl, rfl, rfl⟩ := Embed.inv_Term_Apply hx
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    have hwf := hinv.terms.data k hlt
    rw [hd] at hwf
    obtain ⟨_, _, h3, h4⟩ := hwf
    refine ⟨?_, ?_, ihf x1 rfl he.1, iha x2 rfl he.2⟩
    · intro h1; subst h1
      simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hf
      cases hf with | stuck _ _ hd' => exact h3 hd'
    · intro h2; subst h2
      simp only [Embed.embedded_enc_Term, Embed.enc_Term] at ha
      cases ha with | stuck _ _ hd' => exact h4 hd'
  · intro _ _ _ _ _ _ _ _ x hx _; cases x <;> simp_all [Embed.embedded_enc_Term, Embed.enc_Term, TermValid]
  · trivial
  · intros; trivial

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
