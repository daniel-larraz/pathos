module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Embed
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Node

/-!
# The constructors of the signature

For each constructor that generated code builds or takes apart, what
`construct` gives and what `destruct` finds, under the names the generated
proofs call them by: `CtorSpec.<the Rust name>.construct` and
`.destruct`. A `destruct` lemma has one shape, which the tactic
`pat_destruct` reads: either the value is that constructor of some fields,
which the handles found stand for, or it is not and nothing is found.

Written by hand, for the constructors that the proved programs use.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `=`. -/
theorem CtorSpec.eo__3d.construct (s : Store) (args : Slice Term) (hargs : args.val = [])
    (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.UOp Eo.UserOp.eq)
      | core.result.Result.Err _ => True ⦄div :=
  Store.construct_uop_spec s Eo.UserOp.eq args hargs hinv h64

/-- `not`. -/
theorem CtorSpec.eo_not.construct (s : Store) (args : Slice Term) (hargs : args.val = [])
    (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_not args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.UOp Eo.UserOp.not)
      | core.result.Result.Err _ => True ⦄div :=
  Store.construct_uop_spec s Eo.UserOp.not args hargs hinv h64

/-- `and`. -/
theorem CtorSpec.eo_and.construct (s : Store) (args : Slice Term) (hargs : args.val = [])
    (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_and args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.UOp Eo.UserOp.and)
      | core.result.Result.Err _ => True ⦄div :=
  Store.construct_uop_spec s Eo.UserOp.and args hargs hinv h64

/-- The empty state. -/
theorem CtorSpec.eo__24emb_5fs_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fs_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t Eo.CState.nil
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fs_2enil args []
    hinv h64 rfl (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨by simpa [Embed.embedded_enc_CState, Embed.enc_CState] using hr,
      by simp [Embed.embedded_emb_CState, Embed.emb_CState]⟩

/-- A proof `pf F`. -/
theorem CtorSpec.eo__24eo_5fpf.destruct {s : Store} {t : Term} {p : Eo.Proof}
    (h : Represents.rep s t p) :
    (∃ f v F, p = Eo.Proof.pf F ∧ v.val = [f] ∧ s.Rep f F ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ F, p ≠ Eo.Proof.pf F) ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24eo_5fpf rfl h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨F, rfl, rfl⟩ := Embed.inv_Proof_pf hx
    have he := h.2
    simp only [Embed.embedded_emb_Proof, Embed.emb_Proof] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f _ _ _ hf hn =>
      cases hn
      exact Or.inl ⟨f, v, F, rfl, hvl, ⟨hf, he⟩, hd⟩
  · exact Or.inr ⟨fun F he => hne [Embed.enc_Term F]
      (by subst he; simp [Embed.embedded_enc_Proof, Embed.enc_Proof]), hd⟩

/-- A state `cons o S`. -/
theorem CtorSpec.eo__24emb_5fs_2econs.destruct {s : Store} {t : Term} {S : Eo.CState}
    (h : Represents.rep s t S) :
    (∃ so tl v o S', S = Eo.CState.cons o S' ∧ v.val = [so, tl] ∧ Represents.rep s so o ∧
      Represents.rep s tl S' ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ o S', S ≠ Eo.CState.cons o S') ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t
        = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fs_2econs rfl h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨o, S', rfl, rfl⟩ := Embed.inv_CState_cons hx
    have he := h.2
    simp only [Embed.embedded_emb_CState, Embed.emb_CState] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons so _ _ _ h0 hn =>
      cases hn with
      | cons tl _ _ _ h1 hn' =>
        cases hn'
        exact Or.inl ⟨so, tl, v, o, S', rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun o S' he => hne [Embed.enc_CStateObj o, Embed.enc_CState S']
      (by subst he; simp [Embed.embedded_enc_CState, Embed.enc_CState]), hd⟩

/-- A pushed assumption. -/
theorem CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct {s : Store} {t : Term}
    {o : Eo.CStateObj} (h : Represents.rep s t o) :
    (∃ f v F, o = Eo.CStateObj.assume_push F ∧ v.val = [f] ∧ s.Rep f F ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ F, o ≠ Eo.CStateObj.assume_push F) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t
        = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fso_2eassume_5fpush rfl h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨F, rfl, rfl⟩ := Embed.inv_CStateObj_assume_push hx
    have he := h.2
    simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f _ _ _ hf hn =>
      cases hn
      exact Or.inl ⟨f, v, F, rfl, hvl, ⟨hf, he⟩, hd⟩
  · exact Or.inr ⟨fun F he => hne [Embed.enc_Term F]
      (by subst he; simp [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj]), hd⟩

end pathos_compiled_checker
