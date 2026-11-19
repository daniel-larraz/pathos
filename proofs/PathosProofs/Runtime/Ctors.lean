module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Embed
public import PathosProofs.Runtime.Ops

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
      | core.result.Result.Ok t => RepState s' t Eo.CState.nil
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono
    (Store.construct_data_spec s schema.Constructor.eo__24emb_5fs_2enil args hinv h64 rfl)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    simp only at hres ⊢
    obtain ⟨hlt, v, hv, hd⟩ := hres
    exact RepState.nil t v hlt hd (by rw [hv, hargs])

/-- A proof `pf F`. -/
theorem CtorSpec.eo__24eo_5fpf.destruct {s : Store} {t : Term} {p : Eo.Proof}
    (h : RepProof s t p) :
    (∃ f v F, p = Eo.Proof.pf F ∧ v.val = [f] ∧ s.Rep f F ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ F, p ≠ Eo.Proof.pf F) ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t = ok (core.result.Result.Ok none, s)) := by
  rcases h.destruct with h | ⟨rfl, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨(by intro F h; cases h), hd⟩

/-- A state `cons o S`. -/
theorem CtorSpec.eo__24emb_5fs_2econs.destruct {s : Store} {t : Term} {S : Eo.CState}
    (h : RepState s t S) :
    (∃ so tl v o S', S = Eo.CState.cons o S' ∧ v.val = [so, tl] ∧ RepObj s so o ∧
      RepState s tl S' ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ o S', S ≠ Eo.CState.cons o S') ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t
        = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s _ t rfl]
  cases h with
  | nil _ v hlt hd hv => right; exact ⟨(by intro _ _ h; cases h), by simp [hlt, hd]⟩
  | cons _ so tl v o S' hlt hd hv ho hS =>
    left; exact ⟨so, tl, v, o, S', rfl, hv, ho, hS, by simp [hlt, hd]⟩
  | stuck _ v hlt hd hv => right; exact ⟨(by intro _ _ h; cases h), by simp [hlt, hd]⟩

/-- A pushed assumption. -/
theorem CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct {s : Store} {t : Term}
    {o : Eo.CStateObj} (h : RepObj s t o) :
    (∃ f v F, o = Eo.CStateObj.assume_push F ∧ v.val = [f] ∧ s.Rep f F ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ F, o ≠ Eo.CStateObj.assume_push F) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t
        = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s _ t rfl]
  cases h with
  | assume f v F hlt hd hv hf => right; exact ⟨(by intro _ h; cases h), by simp [hlt, hd]⟩
  | assume_push f v F hlt hd hv hf => left; exact ⟨f, v, F, rfl, hv, hf, by simp [hlt, hd]⟩
  | proven f v F hlt hd hv hf => right; exact ⟨(by intro _ h; cases h), by simp [hlt, hd]⟩

end pathos_compiled_checker
