module

public import CpcChecker
public import PathosProofs.Runtime.Node
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

/-- `$emb_r.re_in_sigma_star`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_in_sigma_star)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_in_sigma_star ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_in_sigma_star) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fin_5fsigma_5fstar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_in_sigma_star hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_in_cstring`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fcstring.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_in_cstring)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fcstring.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_in_cstring ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_in_cstring) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcstring (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_in_cstring hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_in_comp`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fcomp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_in_comp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2ere_5fin_5fcomp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_in_comp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_in_comp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fin_5fcomp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_in_comp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_union_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_union_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_union_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_union_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5funion_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_union_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_inter_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_inter_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_inter_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_inter_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5finter_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_inter_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_range_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_range_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_range_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_range_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5frange_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_range_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_contains`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fcontains.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_contains)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fcontains.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_contains ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_contains) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fcontains (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_contains hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_from_int_nemp_dig_range`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_from_int_nemp_dig_range)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_from_int_nemp_dig_range ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_from_int_nemp_dig_range) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fnemp_5fdig_5frange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_from_int_nemp_dig_range hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_from_int_dig_range`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_from_int_dig_range)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_from_int_dig_range ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_from_int_dig_range) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5ffrom_5fint_5fdig_5frange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_from_int_dig_range hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.eq_refl`. -/
theorem CtorSpec.eo__24emb_5fr_2eeq_5frefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eeq_5frefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.eq_refl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eeq_5frefl args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eeq_5frefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.eq_refl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5frefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.eq_refl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5frefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eeq_5frefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_eq_refl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.eq_symm`. -/
theorem CtorSpec.eo__24emb_5fr_2eeq_5fsymm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eeq_5fsymm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.eq_symm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eeq_5fsymm args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eeq_5fsymm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.eq_symm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fsymm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.eq_symm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fsymm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eeq_5fsymm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_eq_symm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.eq_cond_deq`. -/
theorem CtorSpec.eo__24emb_5fr_2eeq_5fcond_5fdeq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.eq_cond_deq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eeq_5fcond_5fdeq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.eq_cond_deq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.eq_cond_deq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eeq_5fcond_5fdeq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_eq_cond_deq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.eq_ite_lift`. -/
theorem CtorSpec.eo__24emb_5fr_2eeq_5fite_5flift.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.eq_ite_lift)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eeq_5fite_5flift.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.eq_ite_lift ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.eq_ite_lift) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eeq_5fite_5flift (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_eq_ite_lift hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.distinct_binary_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2edistinct_5fbinary_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.distinct_binary_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edistinct_5fbinary_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.distinct_binary_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.distinct_binary_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edistinct_5fbinary_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_distinct_binary_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_bv2nat_int2bv`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_bv2nat_int2bv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_bv2nat_int2bv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_bv2nat_int2bv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_bv2nat_int2bv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_bv2nat_int2bv_extend`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_bv2nat_int2bv_extend)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_bv2nat_int2bv_extend ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_bv2nat_int2bv_extend) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextend (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_bv2nat_int2bv_extend hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_bv2nat_int2bv_extract`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_bv2nat_int2bv_extract)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_bv2nat_int2bv_extract ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_bv2nat_int2bv_extract) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fint2bv_5fextract (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_bv2nat_int2bv_extract hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_int2bv_bv2nat`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_int2bv_bv2nat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_int2bv_bv2nat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_int2bv_bv2nat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbv2nat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_int2bv_bv2nat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_bv2nat_geq_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_bv2nat_geq_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_bv2nat_geq_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_bv2nat_geq_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fbv2nat_5fgeq_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_bv2nat_geq_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_int2bv_bvult_equiv`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_int2bv_bvult_equiv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_int2bv_bvult_equiv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_int2bv_bvult_equiv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvult_5fequiv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_int2bv_bvult_equiv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_int2bv_bvule_equiv`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_int2bv_bvule_equiv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_int2bv_bvule_equiv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_int2bv_bvule_equiv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fint2bv_5fbvule_5fequiv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_int2bv_bvule_equiv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.uf_sbv_to_int_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.uf_sbv_to_int_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.uf_sbv_to_int_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.uf_sbv_to_int_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2euf_5fsbv_5fto_5fint_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_uf_sbv_to_int_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.evaluate`. -/
theorem CtorSpec.eo__24emb_5fr_2eevaluate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eevaluate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.evaluate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eevaluate args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eevaluate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.evaluate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eevaluate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.evaluate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eevaluate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eevaluate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_evaluate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.distinct_values`. -/
theorem CtorSpec.eo__24emb_5fr_2edistinct_5fvalues.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.distinct_values)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edistinct_5fvalues.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.distinct_values ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.distinct_values) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edistinct_5fvalues (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_distinct_values hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.aci_norm`. -/
theorem CtorSpec.eo__24emb_5fr_2eaci_5fnorm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eaci_5fnorm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.aci_norm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eaci_5fnorm args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eaci_5fnorm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.aci_norm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eaci_5fnorm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.aci_norm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eaci_5fnorm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eaci_5fnorm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_aci_norm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.absorb`. -/
theorem CtorSpec.eo__24emb_5fr_2eabsorb.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eabsorb args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.absorb)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eabsorb args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2eabsorb.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.absorb ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eabsorb t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.absorb) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eabsorb t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eabsorb (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_absorb hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.distinct_card_conflict`. -/
theorem CtorSpec.eo__24emb_5fr_2edistinct_5fcard_5fconflict.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.distinct_card_conflict)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CRule, Embed.enc_CRule] using hr
    · simp [Embed.embedded_emb_CRule, Embed.emb_CRule]

theorem CtorSpec.eo__24emb_5fr_2edistinct_5fcard_5fconflict.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.distinct_card_conflict ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.distinct_card_conflict) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edistinct_5fcard_5fconflict (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_distinct_card_conflict hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_s.nil`. -/
theorem CtorSpec.eo__24emb_5fs_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fs_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CState.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fs_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CState, Embed.enc_CState] using hr
    · simp [Embed.embedded_emb_CState, Embed.emb_CState]

theorem CtorSpec.eo__24emb_5fs_2enil.destruct {s : Store} {t : Term} {x : Eo.CState}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CState.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CState.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fs_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CState_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CState, Embed.enc_CState]), hd⟩

/-- `$emb_s.Stuck`. -/
theorem CtorSpec.eo__24emb_5fs_2eStuck.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fs_2eStuck args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CState.Stuck)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fs_2eStuck args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CState, Embed.enc_CState] using hr
    · simp [Embed.embedded_emb_CState, Embed.emb_CState]

theorem CtorSpec.eo__24emb_5fs_2eStuck.destruct {s : Store} {t : Term} {x : Eo.CState}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CState.Stuck ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2eStuck t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CState.Stuck) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2eStuck t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fs_2eStuck (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CState_Stuck hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CState, Embed.enc_CState]), hd⟩

/-- `$emb_s.cons`. -/
theorem CtorSpec.eo__24emb_5fs_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.CStateObj} {a1 : Term} {x1 : Eo.CState}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fs_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CState.cons x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fs_2econs args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CState, Embed.enc_CState] using hr
    · simp only [Embed.embedded_emb_CState, Embed.emb_CState]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fs_2econs.destruct {s : Store} {t : Term} {x : Eo.CState}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.CStateObj) (x1 : Eo.CState), x = Eo.CState.cons x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.CStateObj) (x1 : Eo.CState), x ≠ Eo.CState.cons x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fs_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CState_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CState, Embed.emb_CState] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_CState, Embed.enc_CState]), hd⟩

/-- `$emb_so.assume`. -/
theorem CtorSpec.eo__24emb_5fso_2eassume.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fso_2eassume args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CStateObj.assume x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fso_2eassume args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj] using hr
    · simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj]
      exact h0.2

theorem CtorSpec.eo__24emb_5fso_2eassume.destruct {s : Store} {t : Term} {x : Eo.CStateObj}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term), x = Eo.CStateObj.assume x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term), x ≠ Eo.CStateObj.assume x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fso_2eassume (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CStateObj_assume hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj]), hd⟩

/-- `$emb_so.assume_push`. -/
theorem CtorSpec.eo__24emb_5fso_2eassume_5fpush.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CStateObj.assume_push x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fso_2eassume_5fpush args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj] using hr
    · simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj]
      exact h0.2

theorem CtorSpec.eo__24emb_5fso_2eassume_5fpush.destruct {s : Store} {t : Term} {x : Eo.CStateObj}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term), x = Eo.CStateObj.assume_push x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term), x ≠ Eo.CStateObj.assume_push x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fso_2eassume_5fpush (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CStateObj_assume_push hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj]), hd⟩

/-- `$emb_so.proven`. -/
theorem CtorSpec.eo__24emb_5fso_2eproven.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fso_2eproven args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CStateObj.proven x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fso_2eproven args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj] using hr
    · simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj]
      exact h0.2

theorem CtorSpec.eo__24emb_5fso_2eproven.destruct {s : Store} {t : Term} {x : Eo.CStateObj}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term), x = Eo.CStateObj.proven x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eproven t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term), x ≠ Eo.CStateObj.proven x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eproven t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fso_2eproven (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CStateObj_proven hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CStateObj, Embed.emb_CStateObj] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_CStateObj, Embed.enc_CStateObj]), hd⟩

/-- `$emb_edt.null`. -/
theorem CtorSpec.eo__24emb_5fedt_2enull.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fedt_2enull args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Datatype.null)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fedt_2enull args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Datatype, Embed.enc_Datatype] using hr
    · simp [Embed.embedded_emb_Datatype, Embed.emb_Datatype]

theorem CtorSpec.eo__24emb_5fedt_2enull.destruct {s : Store} {t : Term} {x : Eo.Datatype}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Datatype.null ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedt_2enull t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Datatype.null) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedt_2enull t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fedt_2enull (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Datatype_null hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Datatype, Embed.enc_Datatype]), hd⟩

/-- `$emb_edt.sum`. -/
theorem CtorSpec.eo__24emb_5fedt_2esum.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.DatatypeCons} {a1 : Term} {x1 : Eo.Datatype}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fedt_2esum args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Datatype.sum x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fedt_2esum args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Datatype, Embed.enc_Datatype] using hr
    · simp only [Embed.embedded_emb_Datatype, Embed.emb_Datatype]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fedt_2esum.destruct {s : Store} {t : Term} {x : Eo.Datatype}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.DatatypeCons) (x1 : Eo.Datatype), x = Eo.Datatype.sum x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedt_2esum t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.DatatypeCons) (x1 : Eo.Datatype), x ≠ Eo.Datatype.sum x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedt_2esum t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fedt_2esum (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Datatype_sum hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_Datatype, Embed.emb_Datatype] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_Datatype, Embed.enc_Datatype]), hd⟩

/-- `$emb_edtc.unit`. -/
theorem CtorSpec.eo__24emb_5fedtc_2eunit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fedtc_2eunit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.DatatypeCons.unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fedtc_2eunit args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_DatatypeCons, Embed.enc_DatatypeCons] using hr
    · simp [Embed.embedded_emb_DatatypeCons, Embed.emb_DatatypeCons]

theorem CtorSpec.eo__24emb_5fedtc_2eunit.destruct {s : Store} {t : Term} {x : Eo.DatatypeCons}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.DatatypeCons.unit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedtc_2eunit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.DatatypeCons.unit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedtc_2eunit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fedtc_2eunit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_DatatypeCons_unit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_DatatypeCons, Embed.enc_DatatypeCons]), hd⟩

/-- `$emb_edtc.cons`. -/
theorem CtorSpec.eo__24emb_5fedtc_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term} {a1 : Term} {x1 : Eo.DatatypeCons}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fedtc_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.DatatypeCons.cons x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fedtc_2econs args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_DatatypeCons, Embed.enc_DatatypeCons] using hr
    · simp only [Embed.embedded_emb_DatatypeCons, Embed.emb_DatatypeCons]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fedtc_2econs.destruct {s : Store} {t : Term} {x : Eo.DatatypeCons}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term) (x1 : Eo.DatatypeCons), x = Eo.DatatypeCons.cons x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedtc_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term) (x1 : Eo.DatatypeCons), x ≠ Eo.DatatypeCons.cons x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedtc_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fedtc_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_DatatypeCons_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_DatatypeCons, Embed.emb_DatatypeCons] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_DatatypeCons, Embed.enc_DatatypeCons]), hd⟩

/-- `$emb_edd.nil`. -/
theorem CtorSpec.eo__24emb_5fedd_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fedd_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.DatatypeDecl.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fedd_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_DatatypeDecl, Embed.enc_DatatypeDecl] using hr
    · simp [Embed.embedded_emb_DatatypeDecl, Embed.emb_DatatypeDecl]

theorem CtorSpec.eo__24emb_5fedd_2enil.destruct {s : Store} {t : Term} {x : Eo.DatatypeDecl}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.DatatypeDecl.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedd_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.DatatypeDecl.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedd_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fedd_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_DatatypeDecl_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_DatatypeDecl, Embed.enc_DatatypeDecl]), hd⟩

/-- `$emb_edd.cons`. -/
theorem CtorSpec.eo__24emb_5fedd_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Eo.Datatype} {a2 : Term} {x2 : Eo.DatatypeDecl}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fedd_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.DatatypeDecl.cons x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fedd_2econs args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_DatatypeDecl, Embed.enc_DatatypeDecl] using hr
    · simp only [Embed.embedded_emb_DatatypeDecl, Embed.emb_DatatypeDecl]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fedd_2econs.destruct {s : Store} {t : Term} {x : Eo.DatatypeDecl}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Eo.Datatype) (x2 : Eo.DatatypeDecl), x = Eo.DatatypeDecl.cons x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedd_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Eo.Datatype) (x2 : Eo.DatatypeDecl), x ≠ Eo.DatatypeDecl.cons x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fedd_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fedd_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_DatatypeDecl_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_DatatypeDecl, Embed.emb_DatatypeDecl] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_DatatypeDecl, Embed.enc_DatatypeDecl]), hd⟩

/-- `$eo_pf`. -/
theorem CtorSpec.eo__24eo_5fpf.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24eo_5fpf args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Proof.pf x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24eo_5fpf args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Proof, Embed.enc_Proof] using hr
    · simp only [Embed.embedded_emb_Proof, Embed.emb_Proof]
      exact h0.2

theorem CtorSpec.eo__24eo_5fpf.destruct {s : Store} {t : Term} {x : Eo.Proof}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term), x = Eo.Proof.pf x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term), x ≠ Eo.Proof.pf x0) ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24eo_5fpf (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_Proof_pf hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_Proof, Embed.emb_Proof] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_Proof, Embed.enc_Proof]), hd⟩

/-- `$emb_sbd.nil`. -/
theorem CtorSpec.eo__24emb_5fsbd_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsbd_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtBindings.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsbd_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtBindings, Embed.enc_SmtBindings] using hr
    · simp [Embed.embedded_emb_SmtBindings, Embed.emb_SmtBindings]

theorem CtorSpec.eo__24emb_5fsbd_2enil.destruct {s : Store} {t : Term} {x : Smtm.SmtBindings}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtBindings.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsbd_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtBindings.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsbd_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsbd_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtBindings_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtBindings, Embed.enc_SmtBindings]), hd⟩

/-- `$emb_sbd.cons`. -/
theorem CtorSpec.eo__24emb_5fsbd_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType} {a2 : Term} {x2 : Smtm.SmtTerm} {a3 : Term} {x3 : Smtm.SmtBindings}
    (hargs : args.val = [a0, a1, a2, a3]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (h3 : Represents.rep s a3 x3) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsbd_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtBindings.cons x0 x1 x2 x3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsbd_2econs args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2, Embedded.enc x3] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 (HoldsList.cons _ _ _ _ h3.1 HoldsList.nil))))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtBindings, Embed.enc_SmtBindings] using hr
    · simp only [Embed.embedded_emb_SmtBindings, Embed.emb_SmtBindings]
      exact ⟨h0.2, h1.2, h2.2, h3.2⟩

theorem CtorSpec.eo__24emb_5fsbd_2econs.destruct {s : Store} {t : Term} {x : Smtm.SmtBindings}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (f3 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm) (x3 : Smtm.SmtBindings), x = Smtm.SmtBindings.cons x0 x1 x2 x3 ∧ v.val = [f0, f1, f2, f3] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧ Represents.rep s f3 x3 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsbd_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm) (x3 : Smtm.SmtBindings), x ≠ Smtm.SmtBindings.cons x0 x1 x2 x3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsbd_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsbd_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, x3, rfl, rfl⟩ := Embed.inv_SmtBindings_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtBindings, Embed.emb_SmtBindings] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2 with
          | cons f3 _ _ _ h3 hn3 =>
            cases hn3
            exact Or.inl ⟨f0, f1, f2, f3, v, x0, x1, x2, x3, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2.1⟩, ⟨h3, he.2.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 x3 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2, Embedded.enc x3]
      (by subst he; simp [Embed.embedded_enc_SmtBindings, Embed.enc_SmtBindings]), hd⟩

/-- `$emb_dt.null`. -/
theorem CtorSpec.eo__24emb_5fdt_2enull.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fdt_2enull args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtDatatype.null)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fdt_2enull args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtDatatype, Embed.enc_SmtDatatype] using hr
    · simp [Embed.embedded_emb_SmtDatatype, Embed.emb_SmtDatatype]

theorem CtorSpec.eo__24emb_5fdt_2enull.destruct {s : Store} {t : Term} {x : Smtm.SmtDatatype}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtDatatype.null ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdt_2enull t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtDatatype.null) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdt_2enull t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fdt_2enull (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtDatatype_null hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtDatatype, Embed.enc_SmtDatatype]), hd⟩

/-- `$emb_dt.sum`. -/
theorem CtorSpec.eo__24emb_5fdt_2esum.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtDatatypeCons} {a1 : Term} {x1 : Smtm.SmtDatatype}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fdt_2esum args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtDatatype.sum x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fdt_2esum args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtDatatype, Embed.enc_SmtDatatype] using hr
    · simp only [Embed.embedded_emb_SmtDatatype, Embed.emb_SmtDatatype]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fdt_2esum.destruct {s : Store} {t : Term} {x : Smtm.SmtDatatype}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtDatatypeCons) (x1 : Smtm.SmtDatatype), x = Smtm.SmtDatatype.sum x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdt_2esum t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtDatatypeCons) (x1 : Smtm.SmtDatatype), x ≠ Smtm.SmtDatatype.sum x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdt_2esum t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fdt_2esum (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtDatatype_sum hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtDatatype, Embed.emb_SmtDatatype] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtDatatype, Embed.enc_SmtDatatype]), hd⟩

/-- `$emb_dtc.unit`. -/
theorem CtorSpec.eo__24emb_5fdtc_2eunit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fdtc_2eunit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtDatatypeCons.unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fdtc_2eunit args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtDatatypeCons, Embed.enc_SmtDatatypeCons] using hr
    · simp [Embed.embedded_emb_SmtDatatypeCons, Embed.emb_SmtDatatypeCons]

theorem CtorSpec.eo__24emb_5fdtc_2eunit.destruct {s : Store} {t : Term} {x : Smtm.SmtDatatypeCons}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtDatatypeCons.unit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdtc_2eunit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtDatatypeCons.unit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdtc_2eunit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fdtc_2eunit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtDatatypeCons_unit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtDatatypeCons, Embed.enc_SmtDatatypeCons]), hd⟩

/-- `$emb_dtc.cons`. -/
theorem CtorSpec.eo__24emb_5fdtc_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType} {a1 : Term} {x1 : Smtm.SmtDatatypeCons}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fdtc_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtDatatypeCons.cons x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fdtc_2econs args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtDatatypeCons, Embed.enc_SmtDatatypeCons] using hr
    · simp only [Embed.embedded_emb_SmtDatatypeCons, Embed.emb_SmtDatatypeCons]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fdtc_2econs.destruct {s : Store} {t : Term} {x : Smtm.SmtDatatypeCons}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType) (x1 : Smtm.SmtDatatypeCons), x = Smtm.SmtDatatypeCons.cons x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdtc_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType) (x1 : Smtm.SmtDatatypeCons), x ≠ Smtm.SmtDatatypeCons.cons x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdtc_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fdtc_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtDatatypeCons_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtDatatypeCons, Embed.emb_SmtDatatypeCons] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtDatatypeCons, Embed.enc_SmtDatatypeCons]), hd⟩

/-- `$emb_dd.nil`. -/
theorem CtorSpec.eo__24emb_5fdd_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fdd_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtDatatypeDecl.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fdd_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtDatatypeDecl, Embed.enc_SmtDatatypeDecl] using hr
    · simp [Embed.embedded_emb_SmtDatatypeDecl, Embed.emb_SmtDatatypeDecl]

theorem CtorSpec.eo__24emb_5fdd_2enil.destruct {s : Store} {t : Term} {x : Smtm.SmtDatatypeDecl}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtDatatypeDecl.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdd_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtDatatypeDecl.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdd_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fdd_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtDatatypeDecl_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtDatatypeDecl, Embed.enc_SmtDatatypeDecl]), hd⟩

/-- `$emb_dd.cons`. -/
theorem CtorSpec.eo__24emb_5fdd_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtDatatype} {a2 : Term} {x2 : Smtm.SmtDatatypeDecl}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fdd_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtDatatypeDecl.cons x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fdd_2econs args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtDatatypeDecl, Embed.enc_SmtDatatypeDecl] using hr
    · simp only [Embed.embedded_emb_SmtDatatypeDecl, Embed.emb_SmtDatatypeDecl]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fdd_2econs.destruct {s : Store} {t : Term} {x : Smtm.SmtDatatypeDecl}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatype) (x2 : Smtm.SmtDatatypeDecl), x = Smtm.SmtDatatypeDecl.cons x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdd_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatype) (x2 : Smtm.SmtDatatypeDecl), x ≠ Smtm.SmtDatatypeDecl.cons x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fdd_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fdd_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtDatatypeDecl_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtDatatypeDecl, Embed.emb_SmtDatatypeDecl] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtDatatypeDecl, Embed.enc_SmtDatatypeDecl]), hd⟩

/-- `$emb_sm.None`. -/
theorem CtorSpec.eo__24emb_5fsm_2eNone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eNone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.None)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eNone args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]

theorem CtorSpec.eo__24emb_5fsm_2eNone.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtTerm.None ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eNone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtTerm.None) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eNone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eNone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtTerm_None hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.Boolean`. -/
theorem CtorSpec.eo__24emb_5fsm_2eBoolean.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Bool}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eBoolean args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.Boolean x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eBoolean args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eBoolean.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Bool), x = Smtm.SmtTerm.Boolean x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eBoolean t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Bool), x ≠ Smtm.SmtTerm.Boolean x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eBoolean t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eBoolean (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_Boolean hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.Numeral`. -/
theorem CtorSpec.eo__24emb_5fsm_2eNumeral.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Int}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eNumeral args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.Numeral x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eNumeral args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eNumeral.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Int), x = Smtm.SmtTerm.Numeral x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eNumeral t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Int), x ≠ Smtm.SmtTerm.Numeral x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eNumeral t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eNumeral (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_Numeral hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.Rational`. -/
theorem CtorSpec.eo__24emb_5fsm_2eRational.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Rat}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eRational args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.Rational x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eRational args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eRational.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Rat), x = Smtm.SmtTerm.Rational x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eRational t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Rat), x ≠ Smtm.SmtTerm.Rational x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eRational t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eRational (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_Rational hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.String`. -/
theorem CtorSpec.eo__24emb_5fsm_2eString.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eString args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.String x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eString args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eString.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String), x = Smtm.SmtTerm.String x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eString t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String), x ≠ Smtm.SmtTerm.String x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eString t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eString (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_String hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.Binary`. -/
theorem CtorSpec.eo__24emb_5fsm_2eBinary.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Int} {a1 : Term} {x1 : SmtEval.native_Int}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eBinary args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.Binary x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eBinary args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eBinary.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Int) (x1 : SmtEval.native_Int), x = Smtm.SmtTerm.Binary x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eBinary t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Int) (x1 : SmtEval.native_Int), x ≠ Smtm.SmtTerm.Binary x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eBinary t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eBinary (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_Binary hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.Apply`. -/
theorem CtorSpec.eo__24emb_5fsm_2eApply.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eApply args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.Apply x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eApply args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eApply.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.Apply x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eApply t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.Apply x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eApply t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eApply (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_Apply hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.Var`. -/
theorem CtorSpec.eo__24emb_5fsm_2eVar.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eVar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.Var x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eVar args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eVar.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType), x = Smtm.SmtTerm.Var x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eVar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType), x ≠ Smtm.SmtTerm.Var x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eVar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eVar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_Var hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.DtCons`. -/
theorem CtorSpec.eo__24emb_5fsm_2eDtCons.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtDatatypeDecl} {a2 : Term} {x2 : SmtEval.native_Nat}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eDtCons args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.DtCons x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eDtCons args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eDtCons.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl) (x2 : SmtEval.native_Nat), x = Smtm.SmtTerm.DtCons x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eDtCons t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl) (x2 : SmtEval.native_Nat), x ≠ Smtm.SmtTerm.DtCons x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eDtCons t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eDtCons (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_DtCons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.DtSel`. -/
theorem CtorSpec.eo__24emb_5fsm_2eDtSel.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtDatatypeDecl} {a2 : Term} {x2 : SmtEval.native_Nat} {a3 : Term} {x3 : SmtEval.native_Nat}
    (hargs : args.val = [a0, a1, a2, a3]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (h3 : Represents.rep s a3 x3) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eDtSel args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.DtSel x0 x1 x2 x3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eDtSel args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2, Embedded.enc x3] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 (HoldsList.cons _ _ _ _ h3.1 HoldsList.nil))))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2, h3.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eDtSel.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (f3 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl) (x2 : SmtEval.native_Nat) (x3 : SmtEval.native_Nat), x = Smtm.SmtTerm.DtSel x0 x1 x2 x3 ∧ v.val = [f0, f1, f2, f3] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧ Represents.rep s f3 x3 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eDtSel t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl) (x2 : SmtEval.native_Nat) (x3 : SmtEval.native_Nat), x ≠ Smtm.SmtTerm.DtSel x0 x1 x2 x3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eDtSel t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eDtSel (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, x3, rfl, rfl⟩ := Embed.inv_SmtTerm_DtSel hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2 with
          | cons f3 _ _ _ h3 hn3 =>
            cases hn3
            exact Or.inl ⟨f0, f1, f2, f3, v, x0, x1, x2, x3, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2.1⟩, ⟨h3, he.2.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 x3 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2, Embedded.enc x3]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.DtTester`. -/
theorem CtorSpec.eo__24emb_5fsm_2eDtTester.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtDatatypeDecl} {a2 : Term} {x2 : SmtEval.native_Nat}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eDtTester args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.DtTester x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eDtTester args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eDtTester.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl) (x2 : SmtEval.native_Nat), x = Smtm.SmtTerm.DtTester x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eDtTester t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl) (x2 : SmtEval.native_Nat), x ≠ Smtm.SmtTerm.DtTester x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eDtTester t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eDtTester (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_DtTester hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.UConst`. -/
theorem CtorSpec.eo__24emb_5fsm_2eUConst.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eUConst args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.UConst x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eUConst args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eUConst.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType), x = Smtm.SmtTerm.UConst x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eUConst t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType), x ≠ Smtm.SmtTerm.UConst x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eUConst t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eUConst (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_UConst hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.ite`. -/
theorem CtorSpec.eo__24emb_5fsm_2eite.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.ite x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eite args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eite.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.ite x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eite t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.ite x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eite t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eite (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_ite hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.not`. -/
theorem CtorSpec.eo__24emb_5fsm_2enot.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2enot args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.not x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2enot args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2enot.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.not x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2enot t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.not x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2enot t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2enot (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_not hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.or`. -/
theorem CtorSpec.eo__24emb_5fsm_2eor.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.or x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eor args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eor.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.or x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.or x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_or hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.and`. -/
theorem CtorSpec.eo__24emb_5fsm_2eand.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.and x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eand args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eand.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.and x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eand t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.and x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eand t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eand (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_and hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.=>`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_3d_3e.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_3d_3e args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.imp x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_3d_3e args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_3d_3e.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.imp x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3d_3e t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.imp x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3d_3e t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_3d_3e (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_imp hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.xor`. -/
theorem CtorSpec.eo__24emb_5fsm_2exor.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2exor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.xor x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2exor args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2exor.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.xor x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2exor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.xor x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2exor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2exor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_xor hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.=`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_3d.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.eq x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_3d args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_3d.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.eq x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3d t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.eq x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3d t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_3d (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_eq hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.lam`. -/
theorem CtorSpec.eo__24emb_5fsm_2elam.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2elam args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.lam x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2elam args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2elam.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.lam x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2elam t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.lam x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2elam t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2elam (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_lam hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bind`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebind.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtBindings} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebind args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bind x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebind args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebind.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtBindings) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bind x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebind t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtBindings) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bind x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebind t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebind (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bind hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.@purify`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_40purify.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_40purify args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm._at_purify x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_40purify args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2e_40purify.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm._at_purify x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_40purify t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm._at_purify x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_40purify t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_40purify (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm__at_purify hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.+`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_2b.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.plus x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_2b args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_2b.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.plus x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2b t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.plus x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2b t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_2b (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_plus hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.-`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_2d.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_2d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.neg x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_2d args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_2d.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.neg x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2d t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.neg x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2d t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_2d (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_neg hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.*`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_2a.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_2a args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.mult x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_2a args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_2a.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.mult x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2a t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.mult x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2a t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_2a (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_mult hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.<`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_3c.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_3c args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.lt x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_3c args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_3c.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.lt x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3c t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.lt x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3c t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_3c (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_lt hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.<=`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_3c_3d.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_3c_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.leq x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_3c_3d args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_3c_3d.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.leq x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3c_3d t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.leq x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3c_3d t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_3c_3d (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_leq hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.>`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_3e.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_3e args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.gt x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_3e args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_3e.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.gt x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3e t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.gt x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3e t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_3e (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_gt hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.>=`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_3e_3d.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_3e_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.geq x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_3e_3d args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2e_3e_3d.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.geq x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3e_3d t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.geq x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_3e_3d t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_3e_3d (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_geq hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.to_real`. -/
theorem CtorSpec.eo__24emb_5fsm_2eto_5freal.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eto_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.to_real x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eto_5freal args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eto_5freal.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.to_real x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eto_5freal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.to_real x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eto_5freal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eto_5freal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_to_real hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.to_int`. -/
theorem CtorSpec.eo__24emb_5fsm_2eto_5fint.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.to_int x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eto_5fint args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eto_5fint.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.to_int x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eto_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.to_int x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eto_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eto_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_to_int hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.is_int`. -/
theorem CtorSpec.eo__24emb_5fsm_2eis_5fint.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eis_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.is_int x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eis_5fint args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eis_5fint.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.is_int x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eis_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.is_int x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eis_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eis_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_is_int hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.abs`. -/
theorem CtorSpec.eo__24emb_5fsm_2eabs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eabs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.abs x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eabs args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eabs.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.abs x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eabs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.abs x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eabs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eabs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_abs hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.uneg`. -/
theorem CtorSpec.eo__24emb_5fsm_2euneg.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2euneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.uneg x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2euneg args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2euneg.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.uneg x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2euneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.uneg x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2euneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2euneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_uneg hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.div`. -/
theorem CtorSpec.eo__24emb_5fsm_2ediv.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ediv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.div x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ediv args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ediv.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.div x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ediv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.div x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ediv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ediv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_div hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.mod`. -/
theorem CtorSpec.eo__24emb_5fsm_2emod.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2emod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.mod x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2emod args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2emod.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.mod x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2emod t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.mod x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2emod t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2emod (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_mod hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.divisible`. -/
theorem CtorSpec.eo__24emb_5fsm_2edivisible.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2edivisible args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.divisible x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2edivisible args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2edivisible.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.divisible x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2edivisible t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.divisible x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2edivisible t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2edivisible (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_divisible hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.int.pow2`. -/
theorem CtorSpec.eo__24emb_5fsm_2eint_2epow2.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eint_2epow2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.int_pow2 x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eint_2epow2 args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eint_2epow2.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.int_pow2 x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eint_2epow2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.int_pow2 x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eint_2epow2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eint_2epow2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_int_pow2 hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.int.log2`. -/
theorem CtorSpec.eo__24emb_5fsm_2eint_2elog2.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eint_2elog2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.int_log2 x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eint_2elog2 args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eint_2elog2.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.int_log2 x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eint_2elog2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.int_log2 x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eint_2elog2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eint_2elog2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_int_log2 hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.div_total`. -/
theorem CtorSpec.eo__24emb_5fsm_2ediv_5ftotal.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.div_total x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ediv_5ftotal.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.div_total x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.div_total x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ediv_5ftotal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_div_total hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.mod_total`. -/
theorem CtorSpec.eo__24emb_5fsm_2emod_5ftotal.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2emod_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.mod_total x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2emod_5ftotal args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2emod_5ftotal.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.mod_total x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2emod_5ftotal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.mod_total x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2emod_5ftotal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2emod_5ftotal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_mod_total hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.select`. -/
theorem CtorSpec.eo__24emb_5fsm_2eselect.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eselect args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.select x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eselect args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eselect.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.select x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eselect t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.select x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eselect t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eselect (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_select hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.store`. -/
theorem CtorSpec.eo__24emb_5fsm_2estore.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estore args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.store x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estore args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estore.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.store x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estore t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.store x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estore t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estore (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_store hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.map_diff`. -/
theorem CtorSpec.eo__24emb_5fsm_2emap_5fdiff.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2emap_5fdiff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.map_diff x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2emap_5fdiff args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2emap_5fdiff.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.map_diff x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2emap_5fdiff t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.map_diff x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2emap_5fdiff t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2emap_5fdiff (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_map_diff hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.concat`. -/
theorem CtorSpec.eo__24emb_5fsm_2econcat.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2econcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.concat x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2econcat args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2econcat.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.concat x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2econcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.concat x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2econcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2econcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_concat hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.extract`. -/
theorem CtorSpec.eo__24emb_5fsm_2eextract.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eextract args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.extract x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eextract args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2eextract.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.extract x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eextract t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.extract x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eextract t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eextract (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_extract hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.repeat`. -/
theorem CtorSpec.eo__24emb_5fsm_2erepeat.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2erepeat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.repeat x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2erepeat args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2erepeat.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.repeat x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2erepeat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.repeat x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2erepeat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2erepeat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_repeat hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvnot`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvnot.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvnot args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvnot x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvnot args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2ebvnot.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvnot x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnot t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvnot x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnot t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvnot (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_bvnot hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvand`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvand.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvand x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvand args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvand.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvand x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvand t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvand x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvand t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvand (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvand hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvor`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvor.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvor x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvor args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvor.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvor x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvor x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvor hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvnand`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvnand.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvnand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvnand x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvnand args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvnand.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvnand x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnand t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvnand x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnand t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvnand (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvnand hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvnor`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvnor.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvnor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvnor x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvnor args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvnor.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvnor x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvnor x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvnor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvnor hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvxor`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvxor.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvxor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvxor x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvxor args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvxor.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvxor x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvxor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvxor x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvxor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvxor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvxor hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvxnor`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvxnor.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvxnor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvxnor x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvxnor args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvxnor.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvxnor x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvxnor t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvxnor x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvxnor t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvxnor (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvxnor hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvcomp`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvcomp.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvcomp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvcomp x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvcomp args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvcomp.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvcomp x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvcomp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvcomp x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvcomp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvcomp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvcomp hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvneg`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvneg.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvneg x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvneg args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2ebvneg.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvneg x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvneg x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_bvneg hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvadd`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvadd.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvadd args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvadd x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvadd args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvadd.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvadd x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvadd t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvadd x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvadd t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvadd (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvadd hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvmul`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvmul.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvmul args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvmul x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvmul args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvmul.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvmul x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvmul t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvmul x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvmul t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvmul (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvmul hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvudiv`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvudiv.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvudiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvudiv x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvudiv args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvudiv.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvudiv x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvudiv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvudiv x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvudiv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvudiv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvudiv hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvurem`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvurem.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvurem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvurem x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvurem args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvurem.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvurem x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvurem t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvurem x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvurem t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvurem (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvurem hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsub`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsub.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsub args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsub x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsub args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsub.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsub x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsub t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsub x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsub t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsub (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsub hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsdiv`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsdiv.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsdiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsdiv x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsdiv args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsdiv.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsdiv x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsdiv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsdiv x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsdiv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsdiv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsdiv hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsrem`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsrem.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsrem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsrem x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsrem args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsrem.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsrem x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsrem t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsrem x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsrem t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsrem (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsrem hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsmod`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsmod.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsmod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsmod x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsmod args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsmod.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsmod x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsmod t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsmod x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsmod t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsmod (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsmod hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvult`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvult.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvult x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvult args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvult.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvult x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvult t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvult x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvult t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvult (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvult hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvule`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvule.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvule args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvule x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvule args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvule.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvule x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvule t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvule x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvule t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvule (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvule hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvugt`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvugt.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvugt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvugt x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvugt args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvugt.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvugt x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvugt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvugt x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvugt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvugt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvugt hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvuge`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvuge.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvuge args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvuge x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvuge args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvuge.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvuge x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvuge t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvuge x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvuge t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvuge (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvuge hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvslt`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvslt.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvslt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvslt x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvslt args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvslt.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvslt x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvslt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvslt x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvslt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvslt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvslt hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsle`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsle.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsle args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsle x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsle args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsle.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsle x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsle t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsle x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsle t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsle (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsle hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsgt`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsgt.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsgt x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsgt args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsgt.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsgt x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsgt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsgt x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsgt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsgt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsgt hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsge`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsge.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsge args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsge x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsge args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsge.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsge x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsge t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsge x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsge t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsge (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsge hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvshl`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvshl.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvshl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvshl x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvshl args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvshl.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvshl x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvshl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvshl x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvshl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvshl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvshl hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvlshr`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvlshr.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvlshr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvlshr x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvlshr args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvlshr.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvlshr x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvlshr t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvlshr x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvlshr t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvlshr (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvlshr hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvashr`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvashr.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvashr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvashr x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvashr args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvashr.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvashr x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvashr t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvashr x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvashr t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvashr (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvashr hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.zero_extend`. -/
theorem CtorSpec.eo__24emb_5fsm_2ezero_5fextend.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ezero_5fextend args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.zero_extend x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ezero_5fextend args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ezero_5fextend.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.zero_extend x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ezero_5fextend t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.zero_extend x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ezero_5fextend t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ezero_5fextend (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_zero_extend hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.sign_extend`. -/
theorem CtorSpec.eo__24emb_5fsm_2esign_5fextend.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2esign_5fextend args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.sign_extend x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2esign_5fextend args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2esign_5fextend.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.sign_extend x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2esign_5fextend t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.sign_extend x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2esign_5fextend t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2esign_5fextend (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_sign_extend hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.rotate_left`. -/
theorem CtorSpec.eo__24emb_5fsm_2erotate_5fleft.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2erotate_5fleft args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.rotate_left x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2erotate_5fleft args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2erotate_5fleft.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.rotate_left x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2erotate_5fleft t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.rotate_left x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2erotate_5fleft t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2erotate_5fleft (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_rotate_left hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.rotate_right`. -/
theorem CtorSpec.eo__24emb_5fsm_2erotate_5fright.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2erotate_5fright args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.rotate_right x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2erotate_5fright args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2erotate_5fright.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.rotate_right x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2erotate_5fright t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.rotate_right x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2erotate_5fright t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2erotate_5fright (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_rotate_right hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvuaddo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvuaddo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvuaddo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvuaddo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvuaddo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvuaddo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvuaddo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvuaddo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvuaddo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvuaddo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvuaddo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvuaddo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvnego`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvnego.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvnego args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvnego x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvnego args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2ebvnego.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvnego x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnego t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvnego x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvnego t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvnego (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_bvnego hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsaddo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsaddo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsaddo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsaddo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsaddo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsaddo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsaddo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsaddo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsaddo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsaddo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsaddo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsaddo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvumulo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvumulo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvumulo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvumulo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvumulo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvumulo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvumulo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvumulo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvumulo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvumulo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvumulo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvumulo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsmulo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsmulo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsmulo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsmulo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsmulo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsmulo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsmulo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsmulo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsmulo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsmulo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsmulo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsmulo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvusubo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvusubo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvusubo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvusubo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvusubo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvusubo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvusubo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvusubo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvusubo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvusubo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvusubo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvusubo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvssubo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvssubo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvssubo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvssubo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvssubo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvssubo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvssubo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvssubo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvssubo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvssubo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvssubo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvssubo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.bvsdivo`. -/
theorem CtorSpec.eo__24emb_5fsm_2ebvsdivo.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ebvsdivo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.bvsdivo x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ebvsdivo args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2ebvsdivo.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.bvsdivo x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsdivo t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.bvsdivo x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ebvsdivo t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ebvsdivo (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_bvsdivo hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.seq.empty`. -/
theorem CtorSpec.eo__24emb_5fsm_2eseq_2eempty.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eseq_2eempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.seq_empty x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eseq_2eempty args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2eseq_2eempty.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType), x = Smtm.SmtTerm.seq_empty x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_2eempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType), x ≠ Smtm.SmtTerm.seq_empty x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_2eempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eseq_2eempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_seq_empty hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.len`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2elen.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2elen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_len x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2elen args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2estr_2elen.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_len x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2elen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_len x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2elen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2elen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_len hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.++`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2e_2b_2b.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_concat x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2e_2b_2b.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_concat x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_concat x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2e_2b_2b (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_concat hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.substr`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2esubstr.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2esubstr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_substr x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2esubstr args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2esubstr.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_substr x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2esubstr t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_substr x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2esubstr t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2esubstr (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_substr hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.contains`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2econtains.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2econtains args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_contains x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2econtains args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2econtains.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_contains x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2econtains t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_contains x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2econtains t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2econtains (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_contains hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.replace`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_replace x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_replace x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_replace x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2ereplace (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_replace hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.indexof`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eindexof.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_indexof x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2eindexof.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_indexof x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_indexof x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eindexof (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_indexof hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.at`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eat.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_at x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eat args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2eat.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_at x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_at x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_at hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.prefixof`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eprefixof.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_prefixof x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2eprefixof.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_prefixof x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_prefixof x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eprefixof (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_prefixof hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.suffixof`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2esuffixof.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_suffixof x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2esuffixof.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_suffixof x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_suffixof x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2esuffixof (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_suffixof hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.rev`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2erev.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2erev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_rev x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2erev args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2estr_2erev.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_rev x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2erev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_rev x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2erev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2erev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_rev hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.update`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eupdate.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eupdate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_update x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eupdate args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fsm_2estr_2eupdate.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_update x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eupdate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_update x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eupdate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eupdate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_update hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          exact Or.inl ⟨f0, f1, f2, v, x0, x1, x2, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 x2 he => hne [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.to_lower`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5flower.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_to_lower x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5flower.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_to_lower x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_to_lower x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eto_5flower (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_to_lower hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.to_upper`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fupper.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_to_upper x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fupper.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_to_upper x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_to_upper x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fupper (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_to_upper hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.to_code`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fcode.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_to_code x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm] using hr
    · simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm]
      exact h0.2

theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fcode.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_to_code x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_to_code x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fcode (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_to_code hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩


end pathos_compiled_checker
