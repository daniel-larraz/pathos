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

/-- `$emb_r.bv_sub_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsub_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sub_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsub_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sub_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sub_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsub_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sub_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_width_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_width_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_width_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_width_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_width_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_width_one_not`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_width_one_not)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_width_one_not ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_width_one_not) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_width_one_not hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_eq_xor_solve`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_eq_xor_solve)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_eq_xor_solve ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_eq_xor_solve) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_eq_xor_solve hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_eq_not_solve`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_eq_not_solve)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_eq_not_solve ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_eq_not_solve) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_eq_not_solve hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ugt_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fugt_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ugt_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fugt_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ugt_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ugt_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ugt_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_uge_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fuge_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_uge_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fuge_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_uge_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_uge_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fuge_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_uge_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sgt_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsgt_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sgt_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsgt_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sgt_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sgt_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsgt_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sgt_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sge_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsge_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sge_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsge_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sge_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sge_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsge_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sge_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sle_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsle_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sle_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsle_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sle_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sle_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sle_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_redor_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fredor_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_redor_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fredor_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_redor_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_redor_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fredor_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_redor_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_redand_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fredand_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_redand_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fredand_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_redand_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_redand_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fredand_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_redand_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ule_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ule_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ule_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ule_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fule_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ule_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_comp_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fcomp_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_comp_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fcomp_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_comp_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_comp_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fcomp_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_comp_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_rotate_left_eliminate_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_rotate_left_eliminate_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_rotate_left_eliminate_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_rotate_left_eliminate_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_rotate_left_eliminate_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_rotate_left_eliminate_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_rotate_left_eliminate_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_rotate_left_eliminate_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_rotate_left_eliminate_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fleft_5feliminate_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_rotate_left_eliminate_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_rotate_right_eliminate_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_rotate_right_eliminate_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_rotate_right_eliminate_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_rotate_right_eliminate_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_rotate_right_eliminate_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_rotate_right_eliminate_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_rotate_right_eliminate_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_rotate_right_eliminate_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_rotate_right_eliminate_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5frotate_5fright_5feliminate_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_rotate_right_eliminate_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_nand_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnand_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_nand_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnand_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_nand_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_nand_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnand_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_nand_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_nor_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnor_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_nor_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnor_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_nor_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_nor_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnor_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_nor_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xnor_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxnor_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xnor_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxnor_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xnor_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xnor_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxnor_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xnor_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sdiv_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsdiv_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sdiv_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsdiv_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sdiv_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sdiv_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsdiv_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sdiv_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_extend_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_extend_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_extend_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_extend_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_extend_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_uaddo_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fuaddo_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_uaddo_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fuaddo_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_uaddo_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_uaddo_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fuaddo_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_uaddo_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_saddo_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsaddo_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_saddo_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsaddo_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_saddo_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_saddo_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsaddo_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_saddo_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sdivo_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsdivo_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sdivo_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsdivo_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sdivo_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sdivo_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsdivo_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sdivo_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_smod_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsmod_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_smod_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsmod_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_smod_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_smod_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsmod_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_smod_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_srem_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsrem_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_srem_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsrem_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_srem_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_srem_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsrem_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_srem_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_usubo_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fusubo_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_usubo_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fusubo_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_usubo_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_usubo_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fusubo_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_usubo_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ssubo_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fssubo_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ssubo_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fssubo_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ssubo_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ssubo_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fssubo_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ssubo_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_nego_eliminate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnego_5feliminate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_nego_eliminate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnego_5feliminate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_nego_eliminate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_nego_eliminate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnego_5feliminate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_nego_eliminate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_equal_children`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_equal_children)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_equal_children ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_equal_children) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fchildren (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_equal_children hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_const_cond_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_const_cond_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_const_cond_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_const_cond_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_const_cond_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_const_cond_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_const_cond_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_const_cond_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_const_cond_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_const_cond_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_const_children_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_const_children_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_const_children_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_const_children_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_const_children_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_const_children_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_const_children_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_const_children_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_const_children_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fconst_5fchildren_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_const_children_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_equal_cond_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_equal_cond_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_equal_cond_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_equal_cond_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_equal_cond_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_equal_cond_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_equal_cond_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_equal_cond_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_equal_cond_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_equal_cond_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_equal_cond_3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_equal_cond_3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_equal_cond_3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_equal_cond_3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fequal_5fcond_5f3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_equal_cond_3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_merge_then_if`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_merge_then_if)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_merge_then_if ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_merge_then_if) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5fif (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_merge_then_if hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_merge_else_if`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_merge_else_if)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_merge_else_if ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_merge_else_if) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5fif (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_merge_else_if hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_merge_then_else`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_merge_then_else)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_merge_then_else ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_merge_then_else) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5fthen_5felse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_merge_then_else hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ite_merge_else_else`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ite_merge_else_else)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ite_merge_else_else ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ite_merge_else_else) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fite_5fmerge_5felse_5felse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ite_merge_else_else hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_shl_by_const_0`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_shl_by_const_0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_shl_by_const_0 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_shl_by_const_0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f0 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_shl_by_const_0 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_shl_by_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_shl_by_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_shl_by_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_shl_by_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_shl_by_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_shl_by_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_shl_by_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_shl_by_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_shl_by_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fby_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_shl_by_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_lshr_by_const_0`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_lshr_by_const_0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_lshr_by_const_0 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_lshr_by_const_0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f0 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_lshr_by_const_0 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_lshr_by_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_lshr_by_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_lshr_by_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_lshr_by_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_lshr_by_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_lshr_by_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_lshr_by_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_lshr_by_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_lshr_by_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fby_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_lshr_by_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ashr_by_const_0`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ashr_by_const_0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ashr_by_const_0 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ashr_by_const_0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f0 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ashr_by_const_0 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ashr_by_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ashr_by_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ashr_by_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ashr_by_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ashr_by_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ashr_by_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ashr_by_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ashr_by_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ashr_by_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fby_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ashr_by_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_and_concat_pullup`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_and_concat_pullup)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_and_concat_pullup ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_and_concat_pullup) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_and_concat_pullup hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_or_concat_pullup`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_or_concat_pullup)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_or_concat_pullup ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_or_concat_pullup) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_or_concat_pullup hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_concat_pullup`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_concat_pullup)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_concat_pullup ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_concat_pullup) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_concat_pullup hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_and_concat_pullup2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_and_concat_pullup2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_and_concat_pullup2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_and_concat_pullup2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_and_concat_pullup2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_or_concat_pullup2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_or_concat_pullup2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_or_concat_pullup2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_or_concat_pullup2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_or_concat_pullup2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_concat_pullup2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_concat_pullup2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_concat_pullup2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_concat_pullup2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_concat_pullup2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_and_concat_pullup3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_and_concat_pullup3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_and_concat_pullup3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_and_concat_pullup3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fand_5fconcat_5fpullup3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_and_concat_pullup3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_or_concat_pullup3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_or_concat_pullup3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_or_concat_pullup3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_or_concat_pullup3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5for_5fconcat_5fpullup3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_or_concat_pullup3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_concat_pullup3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_concat_pullup3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_concat_pullup3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_concat_pullup3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fconcat_5fpullup3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_concat_pullup3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_duplicate`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fduplicate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_duplicate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fduplicate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_duplicate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_duplicate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fduplicate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_duplicate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_ones`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fones.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_ones)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fones.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_ones ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_ones) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fones (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_ones hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_xor_not`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fnot.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_xor_not)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fxor_5fnot.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_xor_not ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_xor_not) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fxor_5fnot (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_xor_not hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_not_idemp`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fidemp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_not_idemp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fidemp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_not_idemp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_not_idemp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fidemp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_not_idemp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ult_zero_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fzero_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ult_zero_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fzero_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ult_zero_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ult_zero_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ult_zero_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ult_zero_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fzero_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ult_zero_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fzero_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ult_zero_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ult_zero_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fzero_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ult_zero_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ult_self`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ult_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ult_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ult_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ult_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_lt_self`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5flt_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_lt_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5flt_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_lt_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_lt_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5flt_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_lt_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ule_self`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ule_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ule_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ule_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ule_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ule_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ule_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ule_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ule_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ule_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_ule`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fule.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_ule)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fule.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_ule ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_ule) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fule (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_ule hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sle_self`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsle_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sle_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsle_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sle_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sle_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsle_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sle_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ule_max`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5fmax.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ule_max)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fule_5fmax.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ule_max ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ule_max) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fule_5fmax (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ule_max hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_not_ult`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_not_ult)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fnot_5fult.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_not_ult ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_not_ult) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fnot_5fult (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_not_ult hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_mult_pow2_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_mult_pow2_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_mult_pow2_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_mult_pow2_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_mult_pow2_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_mult_pow2_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_mult_pow2_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_mult_pow2_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_mult_pow2_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_mult_pow2_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_mult_pow2_2b`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_mult_pow2_2b)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_mult_pow2_2b ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_mult_pow2_2b) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmult_5fpow2_5f2b (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_mult_pow2_2b hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_extract_mult_leading_bit`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_extract_mult_leading_bit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_extract_mult_leading_bit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_extract_mult_leading_bit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fextract_5fmult_5fleading_5fbit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_extract_mult_leading_bit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_udiv_pow2_not_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_udiv_pow2_not_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_udiv_pow2_not_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_udiv_pow2_not_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fpow2_5fnot_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_udiv_pow2_not_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_udiv_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fudiv_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_udiv_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fudiv_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_udiv_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_udiv_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_udiv_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_udiv_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fudiv_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_udiv_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fudiv_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_udiv_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_udiv_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fudiv_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_udiv_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_urem_pow2_not_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_urem_pow2_not_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_urem_pow2_not_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_urem_pow2_not_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fpow2_5fnot_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_urem_pow2_not_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_urem_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5furem_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_urem_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5furem_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_urem_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_urem_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_urem_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_urem_self`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5furem_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_urem_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5furem_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_urem_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_urem_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5furem_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_urem_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_shl_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_shl_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fshl_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_shl_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_shl_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fshl_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_shl_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_lshr_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_lshr_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5flshr_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_lshr_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_lshr_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5flshr_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_lshr_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ashr_zero`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ashr_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fashr_5fzero.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ashr_zero ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ashr_zero) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fashr_5fzero (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ashr_zero hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ugt_urem`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fugt_5furem.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ugt_urem)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fugt_5furem.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ugt_urem ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ugt_urem) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fugt_5furem (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ugt_urem hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_ult_one`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_ult_one)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fult_5fone.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_ult_one ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_ult_one) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fult_5fone (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_ult_one hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_merge_sign_extend_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_merge_sign_extend_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_merge_sign_extend_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_merge_sign_extend_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_merge_sign_extend_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_merge_sign_extend_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_merge_sign_extend_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_merge_sign_extend_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_merge_sign_extend_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fmerge_5fsign_5fextend_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_merge_sign_extend_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_eq_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_eq_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_eq_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_eq_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_eq_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_eq_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_eq_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_eq_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_eq_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5feq_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_eq_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_extend_eq_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_extend_eq_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_extend_eq_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_extend_eq_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_extend_eq_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_extend_eq_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_extend_eq_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_extend_eq_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_extend_eq_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5feq_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_extend_eq_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_extend_ult_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_extend_ult_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_extend_ult_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_extend_ult_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_extend_ult_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_zero_extend_ult_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_zero_extend_ult_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_zero_extend_ult_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_zero_extend_ult_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fzero_5fextend_5fult_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_zero_extend_ult_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_ult_const_1`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_ult_const_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_ult_const_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_ult_const_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_ult_const_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_ult_const_2`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_ult_const_2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_ult_const_2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_ult_const_2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_ult_const_2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_ult_const_3`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_ult_const_3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_ult_const_3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_ult_const_3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_ult_const_3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_sign_extend_ult_const_4`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_sign_extend_ult_const_4)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_sign_extend_ult_const_4 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_sign_extend_ult_const_4) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_sign_extend_ult_const_4 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_eq_singleton_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_eq_singleton_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_eq_singleton_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_eq_singleton_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5feq_5fsingleton_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_eq_singleton_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_member_singleton`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fmember_5fsingleton.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_member_singleton)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fmember_5fsingleton.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_member_singleton ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_member_singleton) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fmember_5fsingleton (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_member_singleton hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_member_emp`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fmember_5femp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_member_emp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fmember_5femp.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_member_emp ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_member_emp) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fmember_5femp (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_member_emp hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_subset_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fsubset_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_subset_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fsubset_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_subset_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_subset_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fsubset_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_subset_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_insert_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5finsert_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_insert_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5finsert_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_insert_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_insert_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5finsert_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_insert_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_union_comm`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5fcomm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_union_comm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5fcomm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_union_comm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_union_comm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5funion_5fcomm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_union_comm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_inter_comm`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5fcomm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_inter_comm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5fcomm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_inter_comm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_inter_comm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5finter_5fcomm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_inter_comm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_inter_emp1`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5femp1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_inter_emp1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5femp1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_inter_emp1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_inter_emp1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_inter_emp1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_inter_emp2`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5femp2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_inter_emp2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5femp2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_inter_emp2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_inter_emp2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5finter_5femp2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_inter_emp2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_minus_emp1`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5femp1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_minus_emp1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5femp1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_minus_emp1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_minus_emp1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_minus_emp1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_minus_emp2`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5femp2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_minus_emp2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5femp2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_minus_emp2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_minus_emp2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fminus_5femp2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_minus_emp2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_union_emp1`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5femp1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_union_emp1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5femp1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_union_emp1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_union_emp1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_union_emp1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_union_emp2`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5femp2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_union_emp2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5femp2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_union_emp2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_union_emp2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5funion_5femp2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_union_emp2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_inter_member`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5fmember.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_inter_member)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5fmember.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_inter_member ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_inter_member) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5finter_5fmember (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_inter_member hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_minus_member`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5fmember.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_minus_member)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5fmember.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_minus_member ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_minus_member) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fmember (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_minus_member hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_union_member`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5fmember.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_union_member)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5fmember.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_union_member ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_union_member) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5funion_5fmember (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_union_member hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_choose_singleton`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fchoose_5fsingleton.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_choose_singleton)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fchoose_5fsingleton.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_choose_singleton ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_choose_singleton) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fsingleton (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_choose_singleton hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_minus_self`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_minus_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fminus_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_minus_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_minus_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fminus_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_minus_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_union_self`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_union_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5funion_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_union_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_union_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5funion_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_union_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_inter_self`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5fself.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_inter_self)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5finter_5fself.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_inter_self ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_inter_self) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5finter_5fself (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_inter_self hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_is_empty_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fis_5fempty_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_is_empty_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fis_5fempty_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_is_empty_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_is_empty_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fis_5fempty_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_is_empty_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_is_singleton_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_is_singleton_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_is_singleton_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_is_singleton_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fis_5fsingleton_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_is_singleton_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_ctn_false`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_ctn_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_ctn_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_ctn_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_ctn_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_ctn_full_false1`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_ctn_full_false1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_ctn_full_false1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_ctn_full_false1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_ctn_full_false1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_ctn_full_false2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_ctn_full_false2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_ctn_full_false2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_ctn_full_false2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_ctn_full_false2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_eq_len_false`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5flen_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_eq_len_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5feq_5flen_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_eq_len_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_eq_len_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5feq_5flen_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_eq_len_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_empty_str`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_empty_str)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_empty_str ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_empty_str) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_empty_str hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_empty_range`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_empty_range)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_empty_range ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_empty_range) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_empty_range hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_empty_start`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_empty_start)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_empty_start ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_empty_start) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_empty_start hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_empty_start_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_empty_start_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_empty_start_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_empty_start_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_empty_start_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_substr_start_geq_len`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_substr_start_geq_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_substr_start_geq_len ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_substr_start_geq_len) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_substr_start_geq_len hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_eq_empty`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_eq_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_eq_empty ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_eq_empty) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_eq_empty hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_z_eq_empty_leq`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_z_eq_empty_leq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_z_eq_empty_leq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_z_eq_empty_leq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_z_eq_empty_leq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_substr_eq_empty_leq_len`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_substr_eq_empty_leq_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_substr_eq_empty_leq_len ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_substr_eq_empty_leq_len) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_substr_eq_empty_leq_len hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_replace_inv`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5freplace_5finv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_replace_inv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5freplace_5finv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_replace_inv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_replace_inv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5finv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_replace_inv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_replace_all_inv`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_replace_all_inv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_replace_all_inv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_replace_all_inv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_replace_all_inv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_update_inv`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5fupdate_5finv.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_update_inv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5fupdate_5finv.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_update_inv ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_update_inv) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5fupdate_5finv (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_update_inv hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_update_oob`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5foob.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_update_oob)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5foob.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_update_oob ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_update_oob) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5foob (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_update_oob hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_update_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_update_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_update_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_update_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_update_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_update_fit`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5ffit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_update_fit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5ffit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_update_fit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_update_fit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5ffit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_update_fit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_update_concat_fit0`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_update_concat_fit0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_update_concat_fit0 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_update_concat_fit0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_update_concat_fit0 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_update_concat_fit`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_update_concat_fit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_update_concat_fit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_update_concat_fit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_update_concat_fit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_update_in_first_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_update_in_first_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_update_in_first_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_update_in_first_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_update_in_first_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_len_substr_in_range`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_len_substr_in_range)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_len_substr_in_range ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_len_substr_in_range) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_len_substr_in_range hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_clash`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_clash)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_clash ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_clash) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_clash hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_clash_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_clash_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_clash_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_clash_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_clash_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_clash2`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_clash2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_clash2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_clash2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_clash2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_concat_clash2_rev`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_concat_clash2_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_concat_clash2_rev ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_concat_clash2_rev) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_concat_clash2_rev hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩


end pathos_compiled_checker
