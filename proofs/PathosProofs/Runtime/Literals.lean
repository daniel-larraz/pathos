module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops

/-!
# A pattern on an object literal

`destruct` with the constructor of an object literal (`$emb_Boolean`, …)
finds the literal's native value and stores a native copy of it (the
runtime's `Hit::Raw`): unlike the destruct of a data constructor, it
changes the store. Here for Booleans, which need nothing of the trusted
numbers; the numeral and rational ones copy an `Integer` or a `Rational`
and would bring `clone_spec` into use.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

theorem Store.raw_bool_spec (s : Store) (b : Bool) (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Boolean b) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t b
      | core.result.Result.Err _ => True ⦄div :=
  Store.native_bool_spec s b hinv h64

/-- The literal destruct of a Boolean constructor: a copy of a Boolean
literal, nothing for any other. -/
theorem Store.destruct_literal_boolean (l : lit.Lit) :
    Store.destruct_literal Embedding.Boolean l =
      ok (match l with
        | lit.Lit.Boolean b => Hit.Raw (lit.Lit.Boolean b)
        | _ => Hit.Done none) := by
  cases l <;> simp [Store.destruct_literal, Embedding.Insts.CoreCmpPartialEqEmbedding.eq,
    Embedding.read_discriminant, lit.Lit.Insts.CoreCloneClone.clone, lift,
    core.clone.impls.CloneBool.clone]

/-- No term is stored as a node of the Boolean literal's constructor. -/
theorem enc_ne_node_boolean (x : Eo.Term) (xs : List Tree) :
    Embedded.enc x ≠ Tree.node schema.Constructor.eo__24emb_5fBoolean xs :=
  enc_ne_node_of (e := Embedding.Boolean) rfl nofun nofun xs

/-- `destruct` with `$emb_Boolean` on a handle of a term: a handle of the
native Boolean of a Boolean literal, and nothing for any other term. -/
theorem Store.destruct_boolean_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fBoolean t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (f : Term) (b : Bool), x = Eo.Term.Boolean b ∧ v.val = [f] ∧ Represents.rep s' f b
      | core.result.Result.Ok none => ∀ b, x ≠ Eo.Term.Boolean b
      | core.result.Result.Err _ => True ⦄div := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.destruct
  simp only [show schema.Constructor.embedding schema.Constructor.eo__24emb_5fBoolean =
    ok Embedding.Boolean from rfl, Std.bind_ok]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have none_ok : (∀ b, tx ≠ Tree.lit (lit.Lit.Boolean b)) → ∀ b, x ≠ Eo.Term.Boolean b := by
    intro hn b hb; subst hb
    exact hn b (by rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term])
  cases hh with
  | lit _ l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨b, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · simp only [Store.destruct_literal, Embedding.Insts.CoreCmpPartialEqEmbedding.eq,
        Std.bind_ok, decide_true, ite_true, lit.Lit.Insts.CoreCloneClone.clone, lift,
        core.clone.impls.CloneBool.clone]
      step with Store.raw_bool_spec s b hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv1, hg1⟩
      | Ok f =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
          WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, f, b, rfl, rfl, hr⟩
    all_goals
      simp only [Store.destruct_literal_boolean, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun b h => by cases h⟩
  | node _ d v xs _ hd _ =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec schema.Constructor.eo__24emb_5fBoolean
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    simp only [h1, h2, Std.bind_ok]
    have hnd : n1 ≠ n2 := by
      intro he; subst he
      have hdc := schema.Constructor.code_inj h2 h1
      subst hdc
      exact enc_ne_node_boolean x xs hx
    simp only [hnd, ite_false, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun b h => by cases h)⟩
  | _ =>
    rename_i hd
    first
      | (simp only [hd, WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun b h => by cases h)⟩)
      | (rename_i _ hd'
         simp only [hd', WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun b h => by cases h)⟩)

end pathos_compiled_checker
