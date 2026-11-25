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

/-- `$emb_r.str_concat_unify`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_unify)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_unify ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_unify) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_unify hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_unify_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_unify_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_unify_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_unify_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_unify_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_unify_base`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_unify_base)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_unify_base ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_unify_base) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_unify_base hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_unify_base_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_unify_base_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_unify_base_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_unify_base_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_unify_base_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_prefixof_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fprefixof_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_prefixof_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fprefixof_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_prefixof_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_prefixof_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_prefixof_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_suffixof_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsuffixof_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_suffixof_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsuffixof_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_suffixof_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_suffixof_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_suffixof_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_prefixof_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fprefixof_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_prefixof_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fprefixof_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_prefixof_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_prefixof_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_prefixof_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_suffixof_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsuffixof_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_suffixof_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsuffixof_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_suffixof_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_suffixof_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_suffixof_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_prefixof_one`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fprefixof_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_prefixof_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fprefixof_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_prefixof_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_prefixof_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fprefixof_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_prefixof_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_suffixof_one`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsuffixof_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_suffixof_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsuffixof_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_suffixof_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_suffixof_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsuffixof_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_suffixof_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_combine1`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_combine1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_combine1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_combine1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_combine1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_combine2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_combine2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_combine2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_combine2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_combine2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_combine3`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_combine3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_combine3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_combine3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_combine3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_combine4`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine4.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_combine4)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fcombine4.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_combine4 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_combine4) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fcombine4 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_combine4 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_concat1`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fconcat1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_concat1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fconcat1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_concat1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_concat1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_concat1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_concat2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fconcat2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_concat2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fconcat2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_concat2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_concat2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fconcat2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_concat2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_replace`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5freplace.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_replace)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5freplace.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_replace ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_replace) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5freplace (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_replace hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_full`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5ffull.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_full)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5ffull.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_full ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_full) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_full hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_full_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_full_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_full_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_full_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5ffull_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_full_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_refl`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_refl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_refl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_refl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_refl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_concat_find`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_concat_find)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_concat_find ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_concat_find) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_concat_find hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_concat_find_contra`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_concat_find_contra)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_concat_find_contra ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_concat_find_contra) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fconcat_5ffind_5fcontra (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_concat_find_contra hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_split_char`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_split_char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_split_char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_split_char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fsplit_5fchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_split_char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_leq_len_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_leq_len_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_leq_len_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_leq_len_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fleq_5flen_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_leq_len_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_char`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5fchar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5fchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_at_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fat_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_at_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fat_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_at_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_at_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fat_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_at_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_id`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fid.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_id)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fid.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_id ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_id) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fid (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_id hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_prefix`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fprefix.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_prefix)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fprefix.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_prefix ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_prefix) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_prefix hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_prefix_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_prefix_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_prefix_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_prefix_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fprefix_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_prefix_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_no_contains`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_no_contains)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_no_contains ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_no_contains) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fno_5fcontains (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_no_contains hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_find_base`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_find_base)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_find_base ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_find_base) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fbase (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_find_base hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_find_first_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_find_first_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_find_first_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_find_first_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5ffirst_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_find_first_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_empty`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fempty.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_empty ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_empty) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_empty hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_one_pre`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fone_5fpre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_one_pre)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fone_5fpre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_one_pre ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_one_pre) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fone_5fpre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_one_pre hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_find_pre`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_find_pre)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_find_pre ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_find_pre) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5ffind_5fpre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_find_pre hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_all_no_contains`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_all_no_contains)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_all_no_contains ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_all_no_contains) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fno_5fcontains (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_all_no_contains hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_all_find_pre`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_all_find_pre)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_all_find_pre ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_all_find_pre) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind_5fpre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_all_find_pre hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_all_find`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5ffind.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_all_find)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5ffind.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_all_find ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_all_find) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5ffind (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_all_find hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_all_empty`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_all_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fempty.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_all_empty ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_all_empty) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_all_empty hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_all_id`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fid.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_all_id)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fid.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_all_id ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_all_id) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fid (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_all_id hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_all_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_all_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fall_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_all_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_all_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fall_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_all_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_re_none`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5fnone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_re_none)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5fnone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_re_none ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_re_none) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fnone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_re_none hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_re_all_none`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_re_all_none)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_re_all_none ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_re_all_none) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5fnone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_re_all_none hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_concat_rec`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5fconcat_5frec.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_concat_rec)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5fconcat_5frec.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_concat_rec ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_concat_rec) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5fconcat_5frec (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_concat_rec hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_eq_zero_concat_rec`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_eq_zero_concat_rec)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_eq_zero_concat_rec ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_eq_zero_concat_rec) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fconcat_5frec (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_eq_zero_concat_rec hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_eq_zero_base`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_eq_zero_base)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_eq_zero_base ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_eq_zero_base) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5feq_5fzero_5fbase (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_eq_zero_base hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_no_contains`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_no_contains)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_no_contains ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_no_contains) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fno_5fcontains (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_no_contains hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_oob`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5foob.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_oob)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5foob.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_oob ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_oob) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_oob hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_oob2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5foob2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_oob2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5foob2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_oob2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_oob2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5foob2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_oob2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_contains_pre`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_contains_pre)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_contains_pre ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_contains_pre) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fpre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_contains_pre hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_contains_concat_pre`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_contains_concat_pre)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_contains_concat_pre ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_contains_concat_pre) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fcontains_5fconcat_5fpre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_contains_concat_pre hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_prefix_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_prefix_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_prefix_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_prefix_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fprefix_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_prefix_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_len_oob`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5flen_5foob.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_len_oob)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5flen_5foob.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_len_oob ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_len_oob) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_len_oob hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_len_oob2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5flen_5foob2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_len_oob2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5flen_5foob2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_len_oob2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_len_oob2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5flen_5foob2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_len_oob2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_find_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5ffind_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_find_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5ffind_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_find_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_find_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5ffind_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_find_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_eq_irr`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5feq_5firr.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_eq_irr)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5feq_5firr.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_eq_irr ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_eq_irr) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5feq_5firr (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_eq_irr hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_re_none`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fre_5fnone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_re_none)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fre_5fnone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_re_none ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_re_none) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5fnone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_re_none hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_re_emp_re`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_re_emp_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_re_emp_re ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_re_emp_re) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5femp_5fre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_re_emp_re hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_lower_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_lower_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_lower_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_lower_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_lower_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_upper_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_upper_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_upper_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_upper_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_upper_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_lower_upper`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5fupper.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_lower_upper)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5fupper.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_lower_upper ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_lower_upper) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fupper (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_lower_upper hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_lower_idem`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5fidem.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_lower_idem)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5fidem.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_lower_idem ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_lower_idem) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5fidem (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_lower_idem hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_upper_lower`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5flower.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_upper_lower)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5flower.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_upper_lower ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_upper_lower) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flower (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_upper_lower hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_upper_idem`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5fidem.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_upper_idem)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5fidem.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_upper_idem ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_upper_idem) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5fidem (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_upper_idem hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_lower_len`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5flen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_lower_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5flen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_lower_len ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_lower_len) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5flen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_lower_len hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_upper_len`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5flen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_upper_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5flen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_upper_len ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_upper_len) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5flen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_upper_len hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_lower_from_int`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_lower_from_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_lower_from_int ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_lower_from_int) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5flower_5ffrom_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_lower_from_int hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_upper_from_int`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_upper_from_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_upper_from_int ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_upper_from_int) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5fupper_5ffrom_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_upper_from_int hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_to_int_concat_neg_one`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_to_int_concat_neg_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_to_int_concat_neg_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_to_int_concat_neg_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fto_5fint_5fconcat_5fneg_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_to_int_concat_neg_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_is_digit_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fis_5fdigit_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_is_digit_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fis_5fdigit_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_is_digit_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_is_digit_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fis_5fdigit_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_is_digit_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_leq_empty`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_leq_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fempty.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_leq_empty ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_leq_empty) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_leq_empty hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_leq_empty_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fempty_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_leq_empty_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fempty_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_leq_empty_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_leq_empty_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fempty_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_leq_empty_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_leq_concat_false`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_leq_concat_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_leq_concat_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_leq_concat_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_leq_concat_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_leq_concat_true`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_leq_concat_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_leq_concat_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_leq_concat_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_leq_concat_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_leq_concat_base_1`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_leq_concat_base_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_leq_concat_base_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_leq_concat_base_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_leq_concat_base_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_leq_concat_base_2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_leq_concat_base_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_leq_concat_base_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_leq_concat_base_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fleq_5fconcat_5fbase_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_leq_concat_base_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_lt_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flt_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_lt_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flt_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_lt_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_lt_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flt_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_lt_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_from_int_no_ctn_nondigit`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_from_int_no_ctn_nondigit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_from_int_no_ctn_nondigit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_from_int_no_ctn_nondigit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5ffrom_5fint_5fno_5fctn_5fnondigit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_from_int_no_ctn_nondigit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_ctn_contra`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_ctn_contra)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_ctn_contra ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_ctn_contra) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn_5fcontra (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_ctn_contra hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_ctn`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fctn.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_ctn)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fctn.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_ctn ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_ctn) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fctn (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_ctn hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_dual_ctn`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_dual_ctn)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_dual_ctn ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_dual_ctn) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_dual_ctn hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_dual_ctn_false`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_dual_ctn_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_dual_ctn_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_dual_ctn_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fdual_5fctn_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_dual_ctn_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_self_ctn_simp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_self_ctn_simp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_self_ctn_simp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_self_ctn_simp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fself_5fctn_5fsimp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_self_ctn_simp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_emp_ctn_src`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_emp_ctn_src)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_emp_ctn_src ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_emp_ctn_src) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5femp_5fctn_5fsrc (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_emp_ctn_src hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_char_start_eq_len`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_char_start_eq_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_char_start_eq_len ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_char_start_eq_len) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fchar_5fstart_5feq_5flen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_char_start_eq_len hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_repl_char`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_repl_char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_repl_char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_repl_char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_repl_char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_repl_self_tgt_char`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_repl_self_tgt_char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_repl_self_tgt_char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_repl_self_tgt_char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself_5ftgt_5fchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_repl_self_tgt_char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_repl_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_repl_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_repl_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_repl_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_repl_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_contains_repl_tgt`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_contains_repl_tgt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_contains_repl_tgt ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_contains_repl_tgt) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fcontains_5frepl_5ftgt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_contains_repl_tgt hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_len_id`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_len_id)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_len_id ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_len_id) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flen_5fid (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_len_id hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_src_tgt_no_ctn`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_src_tgt_no_ctn)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_src_tgt_no_ctn ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_src_tgt_no_ctn) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5ftgt_5fno_5fctn (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_src_tgt_no_ctn hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_tgt_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_tgt_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_tgt_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_tgt_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_tgt_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_tgt_no_ctn`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_tgt_no_ctn)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_tgt_no_ctn ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_tgt_no_ctn) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5ftgt_5fno_5fctn (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_tgt_no_ctn hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_src_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_src_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_src_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_src_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_src_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_src_inv_no_ctn1`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_src_inv_no_ctn1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_src_inv_no_ctn1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_src_inv_no_ctn1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_src_inv_no_ctn1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_src_inv_no_ctn2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_src_inv_no_ctn2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_src_inv_no_ctn2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_src_inv_no_ctn2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_src_inv_no_ctn2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_src_inv_no_ctn3`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_src_inv_no_ctn3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_src_inv_no_ctn3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_src_inv_no_ctn3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fsrc_5finv_5fno_5fctn3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_src_inv_no_ctn3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_dual_self`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_dual_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_dual_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_dual_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_dual_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_dual_ite1`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_dual_ite1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_dual_ite1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_dual_ite1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_dual_ite1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_dual_ite2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_dual_ite2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_dual_ite2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_dual_ite2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5fdual_5fite2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_dual_ite2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_repl_repl_lookahead_id_simp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_repl_repl_lookahead_id_simp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_repl_repl_lookahead_id_simp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_repl_repl_lookahead_id_simp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5frepl_5frepl_5flookahead_5fid_5fsimp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_repl_repl_lookahead_id_simp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_all_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fall_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_all_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fall_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_all_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_all_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fall_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_all_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_opt_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fopt_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_opt_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fopt_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_opt_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_opt_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fopt_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_opt_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_diff_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fdiff_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_diff_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fdiff_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_diff_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_diff_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fdiff_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_diff_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_plus_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fplus_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_plus_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fplus_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_plus_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_plus_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fplus_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_plus_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_repeat_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5frepeat_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_repeat_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5frepeat_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_repeat_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_repeat_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5frepeat_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_repeat_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_concat_star_swap`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_concat_star_swap)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_concat_star_swap ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_concat_star_swap) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fswap (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_concat_star_swap hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_concat_star_repeat`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_concat_star_repeat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_concat_star_repeat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_concat_star_repeat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5frepeat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_concat_star_repeat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_concat_star_nullable1`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_concat_star_nullable1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_concat_star_nullable1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_concat_star_nullable1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_concat_star_nullable1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_concat_star_nullable2`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_concat_star_nullable2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_concat_star_nullable2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_concat_star_nullable2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fstar_5fnullable2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_concat_star_nullable2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_concat_merge`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fmerge.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_concat_merge)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat_5fmerge.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_concat_merge ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_concat_merge) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fconcat_5fmerge (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_concat_merge hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_union_all`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5funion_5fall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_union_all)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5funion_5fall.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_union_all ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_union_all) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5funion_5fall (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_union_all hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_union_const_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5funion_5fconst_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_union_const_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5funion_5fconst_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_union_const_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_union_const_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5funion_5fconst_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_union_const_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_inter_all`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5fall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_inter_all)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5fall.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_inter_all ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_inter_all) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5finter_5fall (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_inter_all hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_star_none`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5fnone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_star_none)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5fnone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_star_none ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_star_none) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fnone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_star_none hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_star_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_star_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_star_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_star_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fstar_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_star_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_star_star`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5fstar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_star_star)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5fstar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_star_star ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_star_star) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fstar_5fstar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_star_star hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_range_refl`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5frefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_range_refl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5frefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_range_refl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_range_refl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5frange_5frefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_range_refl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_range_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_range_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_range_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_range_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5frange_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_range_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_range_non_singleton_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_range_non_singleton_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_range_non_singleton_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_range_non_singleton_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_range_non_singleton_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_range_non_singleton_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_range_non_singleton_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_range_non_singleton_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_range_non_singleton_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5frange_5fnon_5fsingleton_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_range_non_singleton_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_star_union_char`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5funion_5fchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_star_union_char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5funion_5fchar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_star_union_char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_star_union_char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_star_union_char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_star_union_drop_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_star_union_drop_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_star_union_drop_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_star_union_drop_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fstar_5funion_5fdrop_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_star_union_drop_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_loop_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5floop_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_loop_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5floop_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_loop_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_loop_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5floop_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_loop_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_loop_star`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5floop_5fstar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_loop_star)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5floop_5fstar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_loop_star ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_loop_star) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5floop_5fstar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_loop_star hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_inter_cstring`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5fcstring.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_inter_cstring)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5fcstring.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_inter_cstring ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_inter_cstring) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_inter_cstring hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_inter_cstring_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_inter_cstring_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_inter_cstring_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_inter_cstring_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5finter_5fcstring_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_inter_cstring_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_len_include`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_len_include)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_len_include ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_len_include) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_len_include hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_len_include_pre`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_len_include_pre)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_len_include_pre ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_len_include_pre) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5finclude_5fpre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_len_include_pre hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_len_norm`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_len_norm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_len_norm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_len_norm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5flen_5fnorm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_len_norm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_len_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5flen_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_len_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5flen_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_len_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_len_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5flen_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_len_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_rev_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5frev_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_rev_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5frev_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_rev_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_rev_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5frev_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_rev_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_rev_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5frev_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_rev_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5frev_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_rev_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_rev_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5frev_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_rev_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_self_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_self_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_self_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_self_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_self_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_no_change`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_no_change)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_no_change ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_no_change) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fno_5fchange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_no_change hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_tgt_eq_len`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_tgt_eq_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_tgt_eq_len ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_tgt_eq_len) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5ftgt_5feq_5flen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_tgt_eq_len hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_len_one_emp_prefix`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_len_one_emp_prefix)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_len_one_emp_prefix ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_len_one_emp_prefix) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5flen_5fone_5femp_5fprefix (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_len_one_emp_prefix hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_emp_tgt_nemp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_emp_tgt_nemp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_emp_tgt_nemp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_emp_tgt_nemp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5femp_5ftgt_5fnemp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_emp_tgt_nemp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_nemp_src_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_nemp_src_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_nemp_src_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_nemp_src_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fnemp_5fsrc_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_nemp_src_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_repl_self_src`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_repl_self_src)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_repl_self_src ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_repl_self_src) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5frepl_5fself_5fsrc (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_repl_self_src hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_len_unit`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5flen_5funit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_len_unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5flen_5funit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_len_unit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_len_unit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5flen_5funit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_len_unit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_nth_unit`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5fnth_5funit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_nth_unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5fnth_5funit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_nth_unit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_nth_unit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5funit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_nth_unit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_nth_concat_unit`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_nth_concat_unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_nth_concat_unit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_nth_concat_unit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_nth_concat_unit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_nth_concat_unit_gen`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_nth_concat_unit_gen)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_nth_concat_unit_gen ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_nth_concat_unit_gen) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5fnth_5fconcat_5funit_5fgen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_nth_concat_unit_gen hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_rev_unit`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5frev_5funit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_rev_unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5frev_5funit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_rev_unit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_rev_unit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5frev_5funit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_rev_unit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_in_empty`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_in_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fempty.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_in_empty ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_in_empty) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fin_5fempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_in_empty hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_in_sigma`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fsigma.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_in_sigma)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fsigma.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_in_sigma ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_in_sigma) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_in_sigma hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩


end pathos_compiled_checker
