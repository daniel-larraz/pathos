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

/-- `$emb_sm.str.from_code`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fcode.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_from_code x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fcode.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_from_code x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_from_code x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fcode (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_from_code hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.is_digit`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eis_5fdigit.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_is_digit x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2eis_5fdigit.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_is_digit x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_is_digit x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eis_5fdigit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_is_digit hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.to_int`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fint.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_to_int x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fint.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_to_int x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_to_int x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_to_int hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.from_int`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fint.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_from_int x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2efrom_5fint.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_from_int x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_from_int x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2efrom_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_from_int hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.<`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2e_3c.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_lt x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2e_3c.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_lt x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_lt x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2e_3c (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_lt hx h.2
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

/-- `$emb_sm.str.<=`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2e_3c_3d.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_leq x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2e_3c_3d.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_leq x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_leq x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2e_3c_3d (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_leq hx h.2
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

/-- `$emb_sm.str.replace_all`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_replace_all x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fall.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_replace_all x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_replace_all x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fall (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_replace_all hx h.2
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

/-- `$emb_sm.str.replace_re`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_replace_re x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_replace_re x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_replace_re x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_replace_re hx h.2
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

/-- `$emb_sm.str.replace_re_all`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_replace_re_all x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_replace_re_all x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_replace_re_all x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2ereplace_5fre_5fall (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_replace_re_all hx h.2
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

/-- `$emb_sm.str.indexof_re`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_indexof_re x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_indexof_re x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_indexof_re x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_indexof_re hx h.2
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

/-- `$emb_sm.re.allchar`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2eallchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2eallchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_allchar)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2eallchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2eallchar.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtTerm.re_allchar ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eallchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtTerm.re_allchar) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eallchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2eallchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtTerm_re_allchar hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.none`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2enone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2enone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_none)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2enone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2enone.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtTerm.re_none ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2enone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtTerm.re_none) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2enone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2enone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtTerm_re_none hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.all`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2eall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2eall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_all)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2eall args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2eall.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtTerm.re_all ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eall t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtTerm.re_all) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eall t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2eall (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtTerm_re_all hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.str.to_re`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fre.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_to_re x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2eto_5fre.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_to_re x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_to_re x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eto_5fre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_str_to_re hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.*`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2e_2a.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2a args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_mult x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2e_2a args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2e_2a.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_mult x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2a t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_mult x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2a t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2e_2a (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_re_mult hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.+`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2e_2b.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_plus x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2e_2b.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_plus x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_plus x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2e_2b (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_re_plus hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.^`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2e_5e.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2e_5e args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_exp x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2e_5e args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2e_5e.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_exp x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_5e t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_exp x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_5e t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2e_5e (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_re_exp hx h.2
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

/-- `$emb_sm.re.opt`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2eopt.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2eopt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_opt x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2eopt args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2eopt.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_opt x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eopt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_opt x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eopt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2eopt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_re_opt hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.comp`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2ecomp.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2ecomp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_comp x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2ecomp args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2ecomp.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_comp x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2ecomp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_comp x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2ecomp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2ecomp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_re_comp hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.re.range`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2erange.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2erange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_range x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2erange args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2erange.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_range x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2erange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_range x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2erange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2erange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_re_range hx h.2
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

/-- `$emb_sm.re.++`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2e_2b_2b.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_concat x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2e_2b_2b.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_concat x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_concat x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2e_2b_2b (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_re_concat hx h.2
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

/-- `$emb_sm.re.inter`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2einter.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2einter args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_inter x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2einter args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2einter.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_inter x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2einter t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_inter x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2einter t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2einter (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_re_inter hx h.2
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

/-- `$emb_sm.re.union`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2eunion.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2eunion args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_union x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2eunion args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2eunion.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_union x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eunion t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_union x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eunion t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2eunion (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_re_union hx h.2
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

/-- `$emb_sm.re.diff`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2ediff.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2ediff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_diff x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2ediff args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2ediff.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_diff x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2ediff t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_diff x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2ediff t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2ediff (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_re_diff hx h.2
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

/-- `$emb_sm.re.loop`. -/
theorem CtorSpec.eo__24emb_5fsm_2ere_2eloop.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2ere_2eloop args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.re_loop x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2ere_2eloop args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2ere_2eloop.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.re_loop x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eloop t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.re_loop x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2ere_2eloop t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2ere_2eloop (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_re_loop hx h.2
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

/-- `$emb_sm.str.in_re`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2ein_5fre.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_in_re x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2ein_5fre.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_in_re x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_in_re x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2ein_5fre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_str_in_re hx h.2
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

/-- `$emb_sm.seq.unit`. -/
theorem CtorSpec.eo__24emb_5fsm_2eseq_2eunit.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eseq_2eunit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.seq_unit x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eseq_2eunit args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eseq_2eunit.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.seq_unit x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_2eunit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.seq_unit x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_2eunit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eseq_2eunit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_seq_unit hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.seq.nth`. -/
theorem CtorSpec.eo__24emb_5fsm_2eseq_2enth.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eseq_2enth args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.seq_nth x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eseq_2enth args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eseq_2enth.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.seq_nth x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_2enth t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.seq_nth x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_2enth t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eseq_2enth (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_seq_nth hx h.2
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

/-- `$emb_sm.str.indexof_re_split`. -/
theorem CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.str_indexof_re_split x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.str_indexof_re_split x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.str_indexof_re_split x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2estr_2eindexof_5fre_5fsplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_str_indexof_re_split hx h.2
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

/-- `$emb_sm.seq_diff`. -/
theorem CtorSpec.eo__24emb_5fsm_2eseq_5fdiff.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.seq_diff x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eseq_5fdiff.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.seq_diff x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.seq_diff x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eseq_5fdiff (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_seq_diff hx h.2
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

/-- `$emb_sm.@strings_occur_index`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm._at_strings_occur_index x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm._at_strings_occur_index x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm._at_strings_occur_index x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm__at_strings_occur_index hx h.2
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

/-- `$emb_sm.@strings_occur_index_re`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm._at_strings_occur_index_re x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_40strings_5foccur_5findex_5fre (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm__at_strings_occur_index_re hx h.2
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

/-- `$emb_sm.choice`. -/
theorem CtorSpec.eo__24emb_5fsm_2echoice.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2echoice args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.choice x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2echoice args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2echoice.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.choice x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2echoice t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.choice x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2echoice t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2echoice (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_choice hx h.2
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

/-- `$emb_sm.set.empty`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2eempty.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2eempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_empty x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2eempty args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2eempty.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType), x = Smtm.SmtTerm.set_empty x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2eempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType), x ≠ Smtm.SmtTerm.set_empty x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2eempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2eempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_set_empty hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.set.singleton`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2esingleton.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2esingleton args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_singleton x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2esingleton args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2esingleton.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.set_singleton x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2esingleton t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.set_singleton x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2esingleton t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2esingleton (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_set_singleton hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.set.union`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2eunion.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2eunion args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_union x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2eunion args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2eunion.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.set_union x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2eunion t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.set_union x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2eunion t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2eunion (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_set_union hx h.2
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

/-- `$emb_sm.set.inter`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2einter.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2einter args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_inter x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2einter args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2einter.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.set_inter x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2einter t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.set_inter x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2einter t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2einter (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_set_inter hx h.2
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

/-- `$emb_sm.set.minus`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2eminus.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2eminus args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_minus x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2eminus args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2eminus.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.set_minus x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2eminus t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.set_minus x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2eminus t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2eminus (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_set_minus hx h.2
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

/-- `$emb_sm.set.member`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2emember.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2emember args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_member x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2emember args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2emember.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.set_member x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2emember t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.set_member x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2emember t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2emember (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_set_member hx h.2
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

/-- `$emb_sm.set.subset`. -/
theorem CtorSpec.eo__24emb_5fsm_2eset_2esubset.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eset_2esubset args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.set_subset x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eset_2esubset args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eset_2esubset.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.set_subset x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2esubset t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.set_subset x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eset_2esubset t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eset_2esubset (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_set_subset hx h.2
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

/-- `$emb_sm./`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_2f.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_2f args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.qdiv x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_2f args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2e_2f.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.qdiv x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2f t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.qdiv x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2f t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_2f (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_qdiv hx h.2
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

/-- `$emb_sm./_total`. -/
theorem CtorSpec.eo__24emb_5fsm_2e_2f_5ftotal.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.qdiv_total x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2e_2f_5ftotal.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.qdiv_total x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.qdiv_total x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2e_2f_5ftotal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_qdiv_total hx h.2
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

/-- `$emb_sm.forall`. -/
theorem CtorSpec.eo__24emb_5fsm_2eforall.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eforall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.forall x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eforall args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eforall.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.forall x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eforall t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.forall x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eforall t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eforall (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_forall hx h.2
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

/-- `$emb_sm.exists`. -/
theorem CtorSpec.eo__24emb_5fsm_2eexists.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtType} {a2 : Term} {x2 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eexists args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.exists x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eexists args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eexists.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x = Smtm.SmtTerm.exists x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eexists t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtType) (x2 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.exists x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eexists t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eexists (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_exists hx h.2
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

/-- `$emb_sm.int_to_bv`. -/
theorem CtorSpec.eo__24emb_5fsm_2eint_5fto_5fbv.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm} {a1 : Term} {x1 : Smtm.SmtTerm}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.int_to_bv x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eint_5fto_5fbv.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x = Smtm.SmtTerm.int_to_bv x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm) (x1 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.int_to_bv x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eint_5fto_5fbv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_int_to_bv hx h.2
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

/-- `$emb_sm.ubv_to_int`. -/
theorem CtorSpec.eo__24emb_5fsm_2eubv_5fto_5fint.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.ubv_to_int x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2eubv_5fto_5fint.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.ubv_to_int x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.ubv_to_int x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2eubv_5fto_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_ubv_to_int hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_sm.sbv_to_int`. -/
theorem CtorSpec.eo__24emb_5fsm_2esbv_5fto_5fint.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtTerm}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtTerm.sbv_to_int x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint args [Embedded.enc x0] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fsm_2esbv_5fto_5fint.destruct {s : Store} {t : Term} {x : Smtm.SmtTerm}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtTerm), x = Smtm.SmtTerm.sbv_to_int x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtTerm), x ≠ Smtm.SmtTerm.sbv_to_int x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fsm_2esbv_5fto_5fint (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_sbv_to_int hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtTerm, Embed.enc_SmtTerm]), hd⟩

/-- `$emb_tsm.None`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eNone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eNone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.None)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eNone args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp [Embed.embedded_emb_SmtType, Embed.emb_SmtType]

theorem CtorSpec.eo__24emb_5ftsm_2eNone.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtType.None ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eNone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtType.None) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eNone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eNone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_None hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Bool`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eBool.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eBool args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Bool)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eBool args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp [Embed.embedded_emb_SmtType, Embed.emb_SmtType]

theorem CtorSpec.eo__24emb_5ftsm_2eBool.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtType.Bool ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eBool t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtType.Bool) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eBool t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eBool (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Bool hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Int`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eInt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eInt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eInt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp [Embed.embedded_emb_SmtType, Embed.emb_SmtType]

theorem CtorSpec.eo__24emb_5ftsm_2eInt.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtType.Int ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eInt t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtType.Int) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eInt t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eInt (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Int hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Real`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eReal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eReal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eReal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp [Embed.embedded_emb_SmtType, Embed.emb_SmtType]

theorem CtorSpec.eo__24emb_5ftsm_2eReal.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtType.Real ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eReal t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtType.Real) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eReal t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eReal (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Real hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.RegLan`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eRegLan.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eRegLan args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.RegLan)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eRegLan args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp [Embed.embedded_emb_SmtType, Embed.emb_SmtType]

theorem CtorSpec.eo__24emb_5ftsm_2eRegLan.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtType.RegLan ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eRegLan t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtType.RegLan) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eRegLan t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eRegLan (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_RegLan hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.BitVec`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eBitVec.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Nat}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eBitVec args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.BitVec x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eBitVec args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact h0.2

theorem CtorSpec.eo__24emb_5ftsm_2eBitVec.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Nat), x = Smtm.SmtType.BitVec x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eBitVec t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Nat), x ≠ Smtm.SmtType.BitVec x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eBitVec t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eBitVec (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_BitVec hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Map`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eMap.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType} {a1 : Term} {x1 : Smtm.SmtType}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eMap args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Map x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eMap args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5ftsm_2eMap.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType) (x1 : Smtm.SmtType), x = Smtm.SmtType.Map x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eMap t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType) (x1 : Smtm.SmtType), x ≠ Smtm.SmtType.Map x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eMap t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eMap (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_Map hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Set`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eSet.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eSet args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Set x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eSet args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact h0.2

theorem CtorSpec.eo__24emb_5ftsm_2eSet.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType), x = Smtm.SmtType.Set x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eSet t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType), x ≠ Smtm.SmtType.Set x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eSet t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eSet (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_Set hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Seq`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eSeq.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eSeq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Seq x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eSeq args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact h0.2

theorem CtorSpec.eo__24emb_5ftsm_2eSeq.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType), x = Smtm.SmtType.Seq x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eSeq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType), x ≠ Smtm.SmtType.Seq x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eSeq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eSeq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_Seq hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Char`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eChar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eChar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eChar args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp [Embed.embedded_emb_SmtType, Embed.emb_SmtType]

theorem CtorSpec.eo__24emb_5ftsm_2eChar.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Smtm.SmtType.Char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eChar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Smtm.SmtType.Char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eChar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eChar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.Datatype`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eDatatype.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Smtm.SmtDatatypeDecl}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eDatatype args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.Datatype x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eDatatype args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5ftsm_2eDatatype.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl), x = Smtm.SmtType.Datatype x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eDatatype t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Smtm.SmtDatatypeDecl), x ≠ Smtm.SmtType.Datatype x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eDatatype t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eDatatype (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_Datatype hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.TypeRef`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eTypeRef.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eTypeRef args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.TypeRef x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eTypeRef args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact h0.2

theorem CtorSpec.eo__24emb_5ftsm_2eTypeRef.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String), x = Smtm.SmtType.TypeRef x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eTypeRef t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String), x ≠ Smtm.SmtType.TypeRef x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eTypeRef t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eTypeRef (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_TypeRef hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.USort`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eUSort.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Nat}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eUSort args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.USort x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eUSort args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact h0.2

theorem CtorSpec.eo__24emb_5ftsm_2eUSort.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Nat), x = Smtm.SmtType.USort x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eUSort t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Nat), x ≠ Smtm.SmtType.USort x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eUSort t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eUSort (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_USort hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.FunType`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eFunType.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType} {a1 : Term} {x1 : Smtm.SmtType}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eFunType args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.FunType x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eFunType args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5ftsm_2eFunType.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType) (x1 : Smtm.SmtType), x = Smtm.SmtType.FunType x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eFunType t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType) (x1 : Smtm.SmtType), x ≠ Smtm.SmtType.FunType x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eFunType t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eFunType (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_FunType hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- `$emb_tsm.DtcAppType`. -/
theorem CtorSpec.eo__24emb_5ftsm_2eDtcAppType.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Smtm.SmtType} {a1 : Term} {x1 : Smtm.SmtType}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5ftsm_2eDtcAppType args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Smtm.SmtType.DtcAppType x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5ftsm_2eDtcAppType args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_SmtType, Embed.enc_SmtType] using hr
    · simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5ftsm_2eDtcAppType.destruct {s : Store} {t : Term} {x : Smtm.SmtType}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Smtm.SmtType) (x1 : Smtm.SmtType), x = Smtm.SmtType.DtcAppType x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eDtcAppType t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Smtm.SmtType) (x1 : Smtm.SmtType), x ≠ Smtm.SmtType.DtcAppType x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5ftsm_2eDtcAppType t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5ftsm_2eDtcAppType (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_DtcAppType hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_SmtType, Embed.emb_SmtType] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_SmtType, Embed.enc_SmtType]), hd⟩

/-- The user operator `Int`. -/
theorem CtorSpec.eo_Int.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Int args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Int args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `Real`. -/
theorem CtorSpec.eo_Real.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Real args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Real args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `BitVec`. -/
theorem CtorSpec.eo_BitVec.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_BitVec args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.BitVec)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_BitVec args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `Char`. -/
theorem CtorSpec.eo_Char.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Char args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Char args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `Seq`. -/
theorem CtorSpec.eo_Seq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Seq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Seq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Seq args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@@Pair`. -/
theorem CtorSpec.eo__40_40Pair.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40Pair args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_Pair)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40Pair args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@@pair`. -/
theorem CtorSpec.eo__40_40pair.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40pair args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_pair)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40pair args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@@TypedList`. -/
theorem CtorSpec.eo__40_40TypedList.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40TypedList args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_TypedList)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40TypedList args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@@TypedList.nil`. -/
theorem CtorSpec.eo__40_40TypedList_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40TypedList_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_TypedList_nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40TypedList_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@@TypedList.cons`. -/
theorem CtorSpec.eo__40_40TypedList_2econs.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40TypedList_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_TypedList_cons)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40TypedList_2econs args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `ite`. -/
theorem CtorSpec.eo_ite.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_ite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.ite)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_ite args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `not`. -/
theorem CtorSpec.eo_not.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_not args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.not)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_not args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `or`. -/
theorem CtorSpec.eo_or.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_or args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.or)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_or args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `and`. -/
theorem CtorSpec.eo_and.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_and args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.and)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_and args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `=>`. -/
theorem CtorSpec.eo__3d_3e.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3d_3e args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.imp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__3d_3e args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `xor`. -/
theorem CtorSpec.eo_xor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_xor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.xor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_xor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `=`. -/
theorem CtorSpec.eo__3d.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__3d args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `lambda`. -/
theorem CtorSpec.eo_lambda.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_lambda args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.lambda)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_lambda args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `distinct`. -/
theorem CtorSpec.eo_distinct.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_distinct args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.distinct)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_distinct args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@purify`. -/
theorem CtorSpec.eo__40purify.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40purify args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_purify)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40purify args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `+`. -/
theorem CtorSpec.eo__2b.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.plus)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__2b args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `-`. -/
theorem CtorSpec.eo__2d.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__2d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__2d args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `*`. -/
theorem CtorSpec.eo__2a.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__2a args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.mult)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__2a args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `<`. -/
theorem CtorSpec.eo__3c.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3c args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.lt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__3c args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `<=`. -/
theorem CtorSpec.eo__3c_3d.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3c_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.leq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__3c_3d args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `>`. -/
theorem CtorSpec.eo__3e.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3e args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.gt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__3e args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `>=`. -/
theorem CtorSpec.eo__3e_3d.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__3e_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.geq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__3e_3d args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `to_real`. -/
theorem CtorSpec.eo_to_5freal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_to_5freal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.to_real)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_to_5freal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `to_int`. -/
theorem CtorSpec.eo_to_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_to_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.to_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_to_5fint args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `is_int`. -/
theorem CtorSpec.eo_is_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_is_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.is_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_is_5fint args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `abs`. -/
theorem CtorSpec.eo_abs.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_abs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.abs)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_abs args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `$eoo_-.2`. -/
theorem CtorSpec.eo__24eoo_5f_2d_2e2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24eoo_5f_2d_2e2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.__eoo_neg_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24eoo_5f_2d_2e2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `div`. -/
theorem CtorSpec.eo_div.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_div args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.div)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_div args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `mod`. -/
theorem CtorSpec.eo_mod.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_mod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.mod)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_mod args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `divisible`. -/
theorem CtorSpec.eo_divisible.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_divisible args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.divisible)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_divisible args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `int.pow2`. -/
theorem CtorSpec.eo_int_2epow2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_int_2epow2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.int_pow2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_int_2epow2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `int.log2`. -/
theorem CtorSpec.eo_int_2elog2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_int_2elog2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.int_log2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_int_2elog2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `int.ispow2`. -/
theorem CtorSpec.eo_int_2eispow2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_int_2eispow2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.int_ispow2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_int_2eispow2 args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `div_total`. -/
theorem CtorSpec.eo_div_5ftotal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_div_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.div_total)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_div_5ftotal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `mod_total`. -/
theorem CtorSpec.eo_mod_5ftotal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_mod_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.mod_total)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_mod_5ftotal args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@int_div_by_zero`. -/
theorem CtorSpec.eo__40int_5fdiv_5fby_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40int_5fdiv_5fby_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_int_div_by_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40int_5fdiv_5fby_5fzero args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@mod_by_zero`. -/
theorem CtorSpec.eo__40mod_5fby_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40mod_5fby_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_mod_by_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40mod_5fby_5fzero args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `Array`. -/
theorem CtorSpec.eo_Array.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Array args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Array)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Array args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `select`. -/
theorem CtorSpec.eo_select.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_select args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.select)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_select args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `store`. -/
theorem CtorSpec.eo_store.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_store args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.store)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_store args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@array_deq_diff`. -/
theorem CtorSpec.eo__40array_5fdeq_5fdiff.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40array_5fdeq_5fdiff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_array_deq_diff)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40array_5fdeq_5fdiff args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `@bvsize`. -/
theorem CtorSpec.eo__40bvsize.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40bvsize args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_bvsize)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40bvsize args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `concat`. -/
theorem CtorSpec.eo_concat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_concat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_concat args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvnot`. -/
theorem CtorSpec.eo_bvnot.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvnot args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvnot)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvnot args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvand`. -/
theorem CtorSpec.eo_bvand.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvand)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvand args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvor`. -/
theorem CtorSpec.eo_bvor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvnand`. -/
theorem CtorSpec.eo_bvnand.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvnand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvnand)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvnand args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvnor`. -/
theorem CtorSpec.eo_bvnor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvnor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvnor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvnor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvxor`. -/
theorem CtorSpec.eo_bvxor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvxor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvxor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvxor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvxnor`. -/
theorem CtorSpec.eo_bvxnor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvxnor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvxnor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvxnor args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvcomp`. -/
theorem CtorSpec.eo_bvcomp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvcomp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvcomp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvcomp args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvneg`. -/
theorem CtorSpec.eo_bvneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvneg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvneg args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvadd`. -/
theorem CtorSpec.eo_bvadd.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvadd args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvadd)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvadd args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvmul`. -/
theorem CtorSpec.eo_bvmul.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvmul args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvmul)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvmul args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvudiv`. -/
theorem CtorSpec.eo_bvudiv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvudiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvudiv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvudiv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvurem`. -/
theorem CtorSpec.eo_bvurem.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvurem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvurem)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvurem args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsub`. -/
theorem CtorSpec.eo_bvsub.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsub args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsub)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsub args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsdiv`. -/
theorem CtorSpec.eo_bvsdiv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsdiv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsdiv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsdiv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsrem`. -/
theorem CtorSpec.eo_bvsrem.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsrem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsrem)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsrem args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsmod`. -/
theorem CtorSpec.eo_bvsmod.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsmod args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsmod)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsmod args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvult`. -/
theorem CtorSpec.eo_bvult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvult)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvult args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvule`. -/
theorem CtorSpec.eo_bvule.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvule args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvule)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvule args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvugt`. -/
theorem CtorSpec.eo_bvugt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvugt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvugt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvugt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvuge`. -/
theorem CtorSpec.eo_bvuge.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvuge args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvuge)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvuge args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvslt`. -/
theorem CtorSpec.eo_bvslt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvslt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvslt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvslt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsle`. -/
theorem CtorSpec.eo_bvsle.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsle args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsle)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsle args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsgt`. -/
theorem CtorSpec.eo_bvsgt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsgt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsgt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsgt args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsge`. -/
theorem CtorSpec.eo_bvsge.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsge args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsge)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsge args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvshl`. -/
theorem CtorSpec.eo_bvshl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvshl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvshl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvshl args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvlshr`. -/
theorem CtorSpec.eo_bvlshr.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvlshr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvlshr)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvlshr args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvashr`. -/
theorem CtorSpec.eo_bvashr.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvashr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvashr)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvashr args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvite`. -/
theorem CtorSpec.eo_bvite.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvite)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvite args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvuaddo`. -/
theorem CtorSpec.eo_bvuaddo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvuaddo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvuaddo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvuaddo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvnego`. -/
theorem CtorSpec.eo_bvnego.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvnego args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvnego)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvnego args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsaddo`. -/
theorem CtorSpec.eo_bvsaddo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsaddo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsaddo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsaddo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvumulo`. -/
theorem CtorSpec.eo_bvumulo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvumulo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvumulo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvumulo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsmulo`. -/
theorem CtorSpec.eo_bvsmulo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsmulo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsmulo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsmulo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvusubo`. -/
theorem CtorSpec.eo_bvusubo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvusubo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvusubo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvusubo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvssubo`. -/
theorem CtorSpec.eo_bvssubo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvssubo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvssubo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvssubo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsdivo`. -/
theorem CtorSpec.eo_bvsdivo.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsdivo args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsdivo)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsdivo args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvultbv`. -/
theorem CtorSpec.eo_bvultbv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvultbv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvultbv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvultbv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvsltbv`. -/
theorem CtorSpec.eo_bvsltbv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvsltbv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvsltbv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvsltbv args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

/-- The user operator `bvredand`. -/
theorem CtorSpec.eo_bvredand.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvredand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvredand)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvredand args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]


end pathos_compiled_checker
