module

public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import PathosProofs.Runtime.Node
public import PathosProofs.Runtime.Embed
public import CpcEmbed

/-!
What the Rust checker's `construct` and `destruct` do with each data
constructor of the embedding, under the names that rust-meta's generated
proofs give them (`CtorSpec.<the Rust name>.construct`, `.destruct`):
`construct` on handles of the fields gives a handle of the value, and
`destruct` on a handle of a value finds handles of its fields exactly when
the value has that constructor. Each is the generic lemma of pathos's
`Runtime/Node.lean` with the inversion of the constructor's tree.

The constructors the runtime does not store as a node over their fields
(the stuck term, applications, object literals, variables) are not here.

Written by lean-meta with the embedding, for pathos's proofs (its
`CpcCtors.lean`); `CpcChecker` is the Lean of the compiled checker.
-/

@[expose] public section

set_option linter.unusedVariables false
set_option linter.internalConstructors false
set_option maxHeartbeats 10000000

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `$emb_r.alpha_equiv`. -/
theorem CtorSpec.eo__24emb_5fr_2ealpha_5fequiv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.alpha_equiv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ealpha_5fequiv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.alpha_equiv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.alpha_equiv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ealpha_5fequiv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_alpha_equiv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.beta_reduce`. -/
theorem CtorSpec.eo__24emb_5fr_2ebeta_5freduce.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebeta_5freduce args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.beta_reduce)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebeta_5freduce args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebeta_5freduce.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.beta_reduce ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebeta_5freduce t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.beta_reduce) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebeta_5freduce t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebeta_5freduce (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_beta_reduce hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_var_reordering`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fvar_5freordering.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_var_reordering)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fvar_5freordering.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_var_reordering ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_var_reordering) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fvar_5freordering (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_var_reordering hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.exists_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2eexists_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eexists_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.exists_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eexists_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eexists_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.exists_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eexists_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.exists_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eexists_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eexists_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_exists_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_unused_vars`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5funused_5fvars.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_unused_vars)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5funused_5fvars.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_unused_vars ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_unused_vars) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5funused_5fvars (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_unused_vars hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_merge_prenex`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fmerge_5fprenex.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_merge_prenex)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fmerge_5fprenex.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_merge_prenex ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_merge_prenex) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fmerge_5fprenex (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_merge_prenex hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_miniscope_and`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fminiscope_5fand.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_miniscope_and)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fminiscope_5fand.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_miniscope_and ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_miniscope_and) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fand (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_miniscope_and hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_miniscope_or`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fminiscope_5for.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_miniscope_or)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fminiscope_5for.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_miniscope_or ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_miniscope_or) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5for (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_miniscope_or hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_miniscope_ite`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fminiscope_5fite.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_miniscope_ite)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fminiscope_5fite.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_miniscope_ite ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_miniscope_ite) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fminiscope_5fite (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_miniscope_ite hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_var_elim_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fvar_5felim_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_var_elim_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fvar_5felim_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_var_elim_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_var_elim_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fvar_5felim_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_var_elim_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.quant_dt_split`. -/
theorem CtorSpec.eo__24emb_5fr_2equant_5fdt_5fsplit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.quant_dt_split)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2equant_5fdt_5fsplit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.quant_dt_split ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.quant_dt_split) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2equant_5fdt_5fsplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_quant_dt_split hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_split`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fsplit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fsplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_split)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fsplit args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fsplit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_split ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fsplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_split) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fsplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fsplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_split hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_inst`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5finst.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5finst args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_inst)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5finst args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5finst.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_inst ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5finst t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_inst) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5finst t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5finst (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_inst hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_collapse_selector`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5fselector.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_collapse_selector)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5fselector.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_collapse_selector ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_collapse_selector) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fselector (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_collapse_selector hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_collapse_tester`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5ftester.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_collapse_tester)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5ftester.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_collapse_tester ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_collapse_tester) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_collapse_tester hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_collapse_tester_singleton`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_collapse_tester_singleton)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_collapse_tester_singleton ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_collapse_tester_singleton) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_collapse_tester_singleton hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_cons_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcons_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_cons_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcons_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_cons_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_cons_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_cons_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_cons_eq_clash`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcons_5feq_5fclash.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_cons_eq_clash)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcons_5feq_5fclash.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_cons_eq_clash ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_cons_eq_clash) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcons_5feq_5fclash (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_cons_eq_clash hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_cycle`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcycle.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcycle args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_cycle)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcycle args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcycle.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_cycle ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcycle t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_cycle) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcycle t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcycle (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_cycle hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_collapse_updater`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5fupdater.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_collapse_updater)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fcollapse_5fupdater.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_collapse_updater ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_collapse_updater) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fcollapse_5fupdater (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_collapse_updater hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.dt_updater_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2edt_5fupdater_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.dt_updater_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edt_5fupdater_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.dt_updater_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.dt_updater_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edt_5fupdater_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_dt_updater_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_div_total_zero_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_div_total_zero_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_div_total_zero_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_div_total_zero_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_div_total_zero_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_div_total_zero_int`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_div_total_zero_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_div_total_zero_int ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_div_total_zero_int) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_div_total_zero_int hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_div_total`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_div_total)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_div_total ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_div_total) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_div_total hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_div_total_one`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_div_total_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_div_total_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_div_total_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_div_total_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_div_total_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_div_total_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_div_total_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_div_total_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_div_total_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_div_total_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_div_total_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_div_total_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_div_total_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_div_total_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_mod_total`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_mod_total)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_mod_total ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_mod_total) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_mod_total hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_mod_total_one`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_mod_total_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_mod_total_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_mod_total_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_mod_total_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_mod_total_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_mod_total_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_mod_total_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_mod_total_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_mod_total_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_mod_total_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_mod_total_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_mod_total_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_mod_total_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_mod_total_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_div_total_over_mod`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_div_total_over_mod)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_div_total_over_mod ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_div_total_over_mod) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_div_total_over_mod hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_elim_gt`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fgt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_elim_gt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fgt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_elim_gt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_elim_gt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5felim_5fgt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_elim_gt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_elim_lt`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5flt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_elim_lt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5flt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_elim_lt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_elim_lt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5felim_5flt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_elim_lt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_elim_int_gt`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fint_5fgt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_elim_int_gt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fint_5fgt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_elim_int_gt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_elim_int_gt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5fgt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_elim_int_gt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_elim_int_lt`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fint_5flt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_elim_int_lt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fint_5flt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_elim_int_lt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_elim_int_lt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5felim_5fint_5flt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_elim_int_lt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_elim_leq`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fleq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_elim_leq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5felim_5fleq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_elim_leq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_elim_leq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5felim_5fleq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_elim_leq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_leq_norm`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fleq_5fnorm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_leq_norm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fleq_5fnorm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_leq_norm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_leq_norm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fnorm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_leq_norm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_geq_tighten`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5ftighten.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_geq_tighten)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5ftighten.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_geq_tighten ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_geq_tighten) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5ftighten (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_geq_tighten hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_geq_norm1_int`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_geq_norm1_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_geq_norm1_int ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_geq_norm1_int) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_geq_norm1_int hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_geq_norm1_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_geq_norm1_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_geq_norm1_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_geq_norm1_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_geq_norm1_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_eq_elim_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5feq_5felim_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_eq_elim_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5feq_5felim_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_eq_elim_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_eq_elim_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_eq_elim_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_eq_elim_int`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5feq_5felim_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_eq_elim_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5feq_5felim_5fint.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_eq_elim_int ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_eq_elim_int) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5feq_5felim_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_eq_elim_int hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_to_int_elim_to_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_to_int_elim_to_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_to_int_elim_to_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_to_int_elim_to_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_to_int_elim_to_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_is_int_elim_to_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_is_int_elim_to_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_is_int_elim_to_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_is_int_elim_to_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_is_int_elim_to_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_div_int_to_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_div_int_to_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_div_int_to_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_div_int_to_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_div_int_to_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_div_total_int_to_real`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_div_total_int_to_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_div_total_int_to_real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_div_total_int_to_real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_div_total_int_to_real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mod_over_mod_1`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mod_over_mod_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mod_over_mod_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mod_over_mod_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mod_over_mod_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mod_over_mod`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmod_5fover_5fmod.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mod_over_mod)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmod_5fover_5fmod.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mod_over_mod ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mod_over_mod) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mod_over_mod hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mod_over_mod_mult`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mod_over_mod_mult)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mod_over_mod_mult ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mod_over_mod_mult) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mod_over_mod_mult hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_eq_conflict`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5feq_5fconflict.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_eq_conflict)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5feq_5fconflict.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_eq_conflict ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_eq_conflict) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5feq_5fconflict (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_eq_conflict hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_int_geq_tighten`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_int_geq_tighten)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_int_geq_tighten ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_int_geq_tighten) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_int_geq_tighten hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_divisible_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fdivisible_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_divisible_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fdivisible_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_divisible_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_divisible_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fdivisible_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_divisible_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_abs_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fabs_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_abs_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fabs_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_abs_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_abs_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fabs_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_abs_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_abs_int_gt`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fabs_5fint_5fgt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_abs_int_gt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fabs_5fint_5fgt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_abs_int_gt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_abs_int_gt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fabs_5fint_5fgt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_abs_int_gt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_abs_real_gt`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fabs_5freal_5fgt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_abs_real_gt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fabs_5freal_5fgt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_abs_real_gt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_abs_real_gt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fabs_5freal_5fgt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_abs_real_gt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_geq_ite_lift`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5fite_5flift.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_geq_ite_lift)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fgeq_5fite_5flift.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_geq_ite_lift ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_geq_ite_lift) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fgeq_5fite_5flift (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_geq_ite_lift hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_leq_ite_lift`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fleq_5fite_5flift.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_leq_ite_lift)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fleq_5fite_5flift.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_leq_ite_lift ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_leq_ite_lift) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fleq_5fite_5flift (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_leq_ite_lift hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_min_lt1`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmin_5flt1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_min_lt1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmin_5flt1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_min_lt1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_min_lt1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_min_lt1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_min_lt2`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmin_5flt2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_min_lt2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmin_5flt2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_min_lt2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_min_lt2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmin_5flt2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_min_lt2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_max_geq1`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmax_5fgeq1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_max_geq1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmax_5fgeq1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_max_geq1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_max_geq1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_max_geq1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_max_geq2`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmax_5fgeq2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_max_geq2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earith_5fmax_5fgeq2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_max_geq2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_max_geq2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmax_5fgeq2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_max_geq2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.array_read_over_write`. -/
theorem CtorSpec.eo__24emb_5fr_2earray_5fread_5fover_5fwrite.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.array_read_over_write)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earray_5fread_5fover_5fwrite.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.array_read_over_write ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.array_read_over_write) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_array_read_over_write hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.array_read_over_write2`. -/
theorem CtorSpec.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.array_read_over_write2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.array_read_over_write2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.array_read_over_write2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_array_read_over_write2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.array_store_overwrite`. -/
theorem CtorSpec.eo__24emb_5fr_2earray_5fstore_5foverwrite.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.array_store_overwrite)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earray_5fstore_5foverwrite.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.array_store_overwrite ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.array_store_overwrite) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earray_5fstore_5foverwrite (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_array_store_overwrite hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.array_store_self`. -/
theorem CtorSpec.eo__24emb_5fr_2earray_5fstore_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.array_store_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earray_5fstore_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.array_store_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.array_store_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_array_store_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.array_read_over_write_split`. -/
theorem CtorSpec.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.array_read_over_write_split)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.array_read_over_write_split ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.array_read_over_write_split) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_array_read_over_write_split hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.array_store_swap`. -/
theorem CtorSpec.eo__24emb_5fr_2earray_5fstore_5fswap.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.array_store_swap)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2earray_5fstore_5fswap.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.array_store_swap ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.array_store_swap) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earray_5fstore_5fswap (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_array_store_swap hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_double_not_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_double_not_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_double_not_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_double_not_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_double_not_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_not_true`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_not_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_not_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_not_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_not_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_not_false`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_not_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_not_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_not_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_not_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_eq_true`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5feq_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_eq_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5feq_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_eq_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_eq_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_eq_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_eq_false`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5feq_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_eq_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5feq_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_eq_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_eq_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5feq_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_eq_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_eq_nrefl`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5feq_5fnrefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_eq_nrefl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5feq_5fnrefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_eq_nrefl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_eq_nrefl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5feq_5fnrefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_eq_nrefl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_impl_false1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ffalse1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_impl_false1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ffalse1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_impl_false1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_impl_false1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_impl_false1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_impl_false2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ffalse2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_impl_false2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ffalse2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_impl_false2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_impl_false2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ffalse2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_impl_false2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_impl_true1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ftrue1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_impl_true1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ftrue1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_impl_true1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_impl_true1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_impl_true1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_impl_true2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ftrue2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_impl_true2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5ftrue2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_impl_true2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_impl_true2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5ftrue2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_impl_true2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_impl_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_impl_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimpl_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_impl_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_impl_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimpl_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_impl_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_dual_impl_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_dual_impl_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_dual_impl_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_dual_impl_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_dual_impl_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_and_conf`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fand_5fconf.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_and_conf)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fand_5fconf.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_and_conf ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_and_conf) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_and_conf hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_and_conf2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fand_5fconf2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_and_conf2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fand_5fconf2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_and_conf2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_and_conf2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fconf2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_and_conf2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_or_taut`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5ftaut.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_or_taut)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5ftaut.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_or_taut ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_or_taut) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_or_taut hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_or_taut2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5ftaut2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_or_taut2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5ftaut2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_or_taut2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_or_taut2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5for_5ftaut2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_or_taut2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_or_de_morgan`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_or_de_morgan)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_or_de_morgan ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_or_de_morgan) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5for_5fde_5fmorgan (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_or_de_morgan hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_implies_de_morgan`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_implies_de_morgan)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_implies_de_morgan ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_implies_de_morgan) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_implies_de_morgan hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_and_de_morgan`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_and_de_morgan)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_and_de_morgan ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_and_de_morgan) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_and_de_morgan hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_or_and_distrib`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_or_and_distrib)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_or_and_distrib ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_or_and_distrib) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5for_5fand_5fdistrib (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_or_and_distrib hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_implies_or_distrib`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_implies_or_distrib)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_implies_or_distrib ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_implies_or_distrib) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_implies_or_distrib hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_xor_refl`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5frefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_xor_refl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5frefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_xor_refl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_xor_refl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5frefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_xor_refl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_xor_nrefl`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5fnrefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_xor_nrefl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5fnrefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_xor_nrefl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_xor_nrefl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fnrefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_xor_nrefl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_xor_false`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_xor_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_xor_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_xor_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_xor_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_xor_true`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_xor_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_xor_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_xor_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_xor_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_xor_comm`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5fcomm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_xor_comm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5fcomm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_xor_comm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_xor_comm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5fcomm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_xor_comm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_xor_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_xor_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fxor_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_xor_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_xor_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fxor_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_xor_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_not_xor_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_not_xor_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_not_xor_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_not_xor_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fxor_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_not_xor_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_not_eq_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_not_eq_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_not_eq_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_not_eq_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_not_eq_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_not_eq_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_not_eq_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_not_eq_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_not_eq_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5feq_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_not_eq_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_neg_branch`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fneg_5fbranch.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_neg_branch)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fneg_5fbranch.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_neg_branch ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_neg_branch) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fneg_5fbranch (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_neg_branch hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_then_true`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_then_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_then_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_then_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_then_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_else_false`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_else_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_else_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_else_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felse_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_else_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_then_false`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_then_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_then_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_then_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fthen_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_then_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_else_true`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_else_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_else_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_else_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felse_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_else_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_then_lookahead_self`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_then_lookahead_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_then_lookahead_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_then_lookahead_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_then_lookahead_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_else_lookahead_self`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5flookahead_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_else_lookahead_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5flookahead_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_else_lookahead_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_else_lookahead_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_else_lookahead_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_then_lookahead_not_self`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_then_lookahead_not_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_then_lookahead_not_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_then_lookahead_not_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_then_lookahead_not_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_else_lookahead_not_self`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_else_lookahead_not_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_else_lookahead_not_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_else_lookahead_not_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_else_lookahead_not_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_expand`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fexpand.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fexpand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_expand)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fexpand args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fexpand.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_expand ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fexpand t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_expand) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fexpand t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fexpand (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_expand hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bool_not_ite_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5fite_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bool_not_ite_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebool_5fnot_5fite_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bool_not_ite_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bool_not_ite_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebool_5fnot_5fite_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bool_not_ite_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_true_cond`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5ftrue_5fcond.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_true_cond)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5ftrue_5fcond.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_true_cond ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_true_cond) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5ftrue_5fcond (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_true_cond hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_false_cond`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5ffalse_5fcond.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_false_cond)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5ffalse_5fcond.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_false_cond ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_false_cond) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5ffalse_5fcond (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_false_cond hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_not_cond`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fnot_5fcond.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_not_cond)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fnot_5fcond.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_not_cond ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_not_cond) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fnot_5fcond (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_not_cond hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_eq_branch`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5feq_5fbranch.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_eq_branch)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5feq_5fbranch.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_eq_branch ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_eq_branch) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5feq_5fbranch (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_eq_branch hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_then_lookahead`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5flookahead.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_then_lookahead)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5flookahead.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_then_lookahead ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_then_lookahead) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fthen_5flookahead (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_then_lookahead hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_else_lookahead`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5flookahead.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_else_lookahead)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5flookahead.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_else_lookahead ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_else_lookahead) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felse_5flookahead (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_else_lookahead hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_then_neg_lookahead`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_then_neg_lookahead)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_then_neg_lookahead ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_then_neg_lookahead) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_then_neg_lookahead hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_else_neg_lookahead`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_else_neg_lookahead)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_else_neg_lookahead ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_else_neg_lookahead) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felse_5fneg_5flookahead (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_else_neg_lookahead hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_concat_extract_merge`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_concat_extract_merge)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_concat_extract_merge ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_concat_extract_merge) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_concat_extract_merge hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_extract`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fextract.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_extract)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fextract.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_extract ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_extract) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fextract (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_extract hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_whole`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fwhole.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_whole)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fwhole.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_whole ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_whole) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fwhole (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_whole hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_concat_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_concat_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_concat_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_concat_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_concat_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_concat_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_concat_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_concat_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_concat_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_concat_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_concat_3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_concat_3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_concat_3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_concat_3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_concat_3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_concat_4`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_concat_4)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_concat_4 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_concat_4) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_concat_4 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_eq_extract_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_eq_extract_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_eq_extract_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_eq_extract_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_eq_extract_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_eq_extract_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_eq_extract_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_eq_extract_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_eq_extract_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_eq_extract_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_eq_extract_elim3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_eq_extract_elim3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_eq_extract_elim3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_eq_extract_elim3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fextract_5felim3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_eq_extract_elim3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_not`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fnot.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_not)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fnot.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_not ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_not) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fnot (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_not hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_sign_extend_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_sign_extend_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_sign_extend_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_sign_extend_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_sign_extend_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_sign_extend_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_sign_extend_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_sign_extend_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_sign_extend_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_sign_extend_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_sign_extend_3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_sign_extend_3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_sign_extend_3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_sign_extend_3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_sign_extend_3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_not_xor`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fxor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_not_xor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fxor.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_not_xor ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_not_xor) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fxor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_not_xor hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_and_simplify_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_and_simplify_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_and_simplify_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_and_simplify_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_and_simplify_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_and_simplify_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_and_simplify_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_and_simplify_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_and_simplify_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_and_simplify_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_or_simplify_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_or_simplify_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_or_simplify_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_or_simplify_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_or_simplify_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_or_simplify_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_or_simplify_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_or_simplify_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_or_simplify_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5for_5fsimplify_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_or_simplify_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_simplify_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_simplify_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_simplify_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_simplify_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_simplify_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_simplify_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_simplify_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_simplify_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_simplify_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_simplify_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_simplify_3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_simplify_3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_simplify_3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_simplify_3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_simplify_3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ult_add_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fadd_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ult_add_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fadd_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ult_add_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ult_add_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fadd_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ult_add_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_mult_slt_mult_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_mult_slt_mult_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_mult_slt_mult_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_mult_slt_mult_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_mult_slt_mult_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_mult_slt_mult_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_mult_slt_mult_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_mult_slt_mult_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_mult_slt_mult_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_mult_slt_mult_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_commutative_xor`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fcommutative_5fxor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_commutative_xor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fcommutative_5fxor.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_commutative_xor ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_commutative_xor) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fxor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_commutative_xor hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_commutative_comp`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fcommutative_5fcomp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_commutative_comp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fcommutative_5fcomp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_commutative_comp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_commutative_comp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fcomp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_commutative_comp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_extend_eliminate_0`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_extend_eliminate_0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_extend_eliminate_0 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_extend_eliminate_0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_extend_eliminate_0 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_eliminate_0`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_eliminate_0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_eliminate_0 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_eliminate_0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_eliminate_0 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_not_neq`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fneq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_not_neq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fneq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_not_neq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_not_neq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fneq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_not_neq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ult_ones`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fones.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ult_ones)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fones.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ult_ones ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ult_ones) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fones (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ult_ones hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_concat_merge_const`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_concat_merge_const)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_concat_merge_const ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_concat_merge_const) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_concat_merge_const hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_commutative_add`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fcommutative_5fadd.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_commutative_add)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil) (fun _ h => by cases h))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ebv_5fcommutative_5fadd.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_commutative_add ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_commutative_add) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fcommutative_5fadd (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_commutative_add hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩


end pathos_compiled_checker
