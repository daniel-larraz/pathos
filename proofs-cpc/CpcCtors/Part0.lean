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

/-- `$emb_al.nil`. -/
theorem CtorSpec.eo__24emb_5fal_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fal_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CArgList.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fal_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CArgList, Embed.enc_CArgList] using hr
    · simp [Embed.embedded_emb_CArgList, Embed.emb_CArgList]

theorem CtorSpec.eo__24emb_5fal_2enil.destruct {s : Store} {t : Term} {x : Eo.CArgList}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CArgList.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fal_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CArgList.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fal_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fal_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CArgList_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CArgList, Embed.enc_CArgList]), hd⟩

/-- `$emb_al.cons`. -/
theorem CtorSpec.eo__24emb_5fal_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term} {a1 : Term} {x1 : Eo.CArgList}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fal_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CArgList.cons x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fal_2econs args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CArgList, Embed.enc_CArgList] using hr
    · simp only [Embed.embedded_emb_CArgList, Embed.emb_CArgList]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fal_2econs.destruct {s : Store} {t : Term} {x : Eo.CArgList}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term) (x1 : Eo.CArgList), x = Eo.CArgList.cons x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fal_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term) (x1 : Eo.CArgList), x ≠ Eo.CArgList.cons x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fal_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fal_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CArgList_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CArgList, Embed.emb_CArgList] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_CArgList, Embed.enc_CArgList]), hd⟩

/-- `$emb_cmd.assume_push`. -/
theorem CtorSpec.eo__24emb_5fcmd_2eassume_5fpush.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CCmd.assume_push x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CCmd, Embed.enc_CCmd] using hr
    · simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd]
      exact h0.2

theorem CtorSpec.eo__24emb_5fcmd_2eassume_5fpush.destruct {s : Store} {t : Term} {x : Eo.CCmd}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term), x = Eo.CCmd.assume_push x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term), x ≠ Eo.CCmd.assume_push x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fcmd_2eassume_5fpush (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CCmd_assume_push hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_CCmd, Embed.enc_CCmd]), hd⟩

/-- `$emb_cmd.check_proven`. -/
theorem CtorSpec.eo__24emb_5fcmd_2echeck_5fproven.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CCmd.check_proven x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CCmd, Embed.enc_CCmd] using hr
    · simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd]
      exact h0.2

theorem CtorSpec.eo__24emb_5fcmd_2echeck_5fproven.destruct {s : Store} {t : Term} {x : Eo.CCmd}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term), x = Eo.CCmd.check_proven x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term), x ≠ Eo.CCmd.check_proven x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fcmd_2echeck_5fproven (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CCmd_check_proven hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_CCmd, Embed.enc_CCmd]), hd⟩

/-- `$emb_cmd.step`. -/
theorem CtorSpec.eo__24emb_5fcmd_2estep.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.CRule} {a1 : Term} {x1 : Eo.CArgList} {a2 : Term} {x2 : Eo.CIndexList}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fcmd_2estep args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CCmd.step x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fcmd_2estep args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CCmd, Embed.enc_CCmd] using hr
    · simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fcmd_2estep.destruct {s : Store} {t : Term} {x : Eo.CCmd}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.CRule) (x1 : Eo.CArgList) (x2 : Eo.CIndexList), x = Eo.CCmd.step x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2estep t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.CRule) (x1 : Eo.CArgList) (x2 : Eo.CIndexList), x ≠ Eo.CCmd.step x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2estep t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fcmd_2estep (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_CCmd_step hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd] at he
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
      (by subst he; simp [Embed.embedded_enc_CCmd, Embed.enc_CCmd]), hd⟩

/-- `$emb_cmd.step_pop`. -/
theorem CtorSpec.eo__24emb_5fcmd_2estep_5fpop.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.CRule} {a1 : Term} {x1 : Eo.CArgList} {a2 : Term} {x2 : Eo.CIndexList}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fcmd_2estep_5fpop args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CCmd.step_pop x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fcmd_2estep_5fpop args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CCmd, Embed.enc_CCmd] using hr
    · simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fcmd_2estep_5fpop.destruct {s : Store} {t : Term} {x : Eo.CCmd}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.CRule) (x1 : Eo.CArgList) (x2 : Eo.CIndexList), x = Eo.CCmd.step_pop x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2estep_5fpop t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.CRule) (x1 : Eo.CArgList) (x2 : Eo.CIndexList), x ≠ Eo.CCmd.step_pop x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmd_2estep_5fpop t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fcmd_2estep_5fpop (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_CCmd_step_pop hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CCmd, Embed.emb_CCmd] at he
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
      (by subst he; simp [Embed.embedded_enc_CCmd, Embed.enc_CCmd]), hd⟩

/-- `$emb_cmdl.nil`. -/
theorem CtorSpec.eo__24emb_5fcmdl_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fcmdl_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CCmdList.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fcmdl_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CCmdList, Embed.enc_CCmdList] using hr
    · simp [Embed.embedded_emb_CCmdList, Embed.emb_CCmdList]

theorem CtorSpec.eo__24emb_5fcmdl_2enil.destruct {s : Store} {t : Term} {x : Eo.CCmdList}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CCmdList.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmdl_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CCmdList.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmdl_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fcmdl_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CCmdList_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CCmdList, Embed.enc_CCmdList]), hd⟩

/-- `$emb_cmdl.cons`. -/
theorem CtorSpec.eo__24emb_5fcmdl_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.CCmd} {a1 : Term} {x1 : Eo.CCmdList}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fcmdl_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CCmdList.cons x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fcmdl_2econs args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CCmdList, Embed.enc_CCmdList] using hr
    · simp only [Embed.embedded_emb_CCmdList, Embed.emb_CCmdList]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fcmdl_2econs.destruct {s : Store} {t : Term} {x : Eo.CCmdList}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.CCmd) (x1 : Eo.CCmdList), x = Eo.CCmdList.cons x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmdl_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.CCmd) (x1 : Eo.CCmdList), x ≠ Eo.CCmdList.cons x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fcmdl_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fcmdl_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CCmdList_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CCmdList, Embed.emb_CCmdList] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_CCmdList, Embed.enc_CCmdList]), hd⟩

/-- `$emb_indl.nil`. -/
theorem CtorSpec.eo__24emb_5findl_2enil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5findl_2enil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CIndexList.nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5findl_2enil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CIndexList, Embed.enc_CIndexList] using hr
    · simp [Embed.embedded_emb_CIndexList, Embed.emb_CIndexList]

theorem CtorSpec.eo__24emb_5findl_2enil.destruct {s : Store} {t : Term} {x : Eo.CIndexList}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CIndexList.nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5findl_2enil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CIndexList.nil) ∧
      Store.destruct s schema.Constructor.eo__24emb_5findl_2enil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5findl_2enil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CIndexList_nil hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CIndexList, Embed.enc_CIndexList]), hd⟩

/-- `$emb_indl.cons`. -/
theorem CtorSpec.eo__24emb_5findl_2econs.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Int} {a1 : Term} {x1 : Eo.CIndexList}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5findl_2econs args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CIndexList.cons x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5findl_2econs args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_CIndexList, Embed.enc_CIndexList] using hr
    · simp only [Embed.embedded_emb_CIndexList, Embed.emb_CIndexList]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5findl_2econs.destruct {s : Store} {t : Term} {x : Eo.CIndexList}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Int) (x1 : Eo.CIndexList), x = Eo.CIndexList.cons x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5findl_2econs t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Int) (x1 : Eo.CIndexList), x ≠ Eo.CIndexList.cons x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5findl_2econs t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5findl_2econs (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CIndexList_cons hx h.2
    have he := h.2
    simp only [Embed.embedded_emb_CIndexList, Embed.emb_CIndexList] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_CIndexList, Embed.enc_CIndexList]), hd⟩

/-- `$emb_r.scope`. -/
theorem CtorSpec.eo__24emb_5fr_2escope.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2escope args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.scope)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2escope args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2escope.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.scope ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2escope t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.scope) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2escope t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2escope (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_scope hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.process_scope`. -/
theorem CtorSpec.eo__24emb_5fr_2eprocess_5fscope.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eprocess_5fscope args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.process_scope)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eprocess_5fscope args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eprocess_5fscope.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.process_scope ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eprocess_5fscope t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.process_scope) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eprocess_5fscope t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eprocess_5fscope (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_process_scope hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eite_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.split`. -/
theorem CtorSpec.eo__24emb_5fr_2esplit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.split)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esplit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esplit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.split ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.split) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_split hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.resolution`. -/
theorem CtorSpec.eo__24emb_5fr_2eresolution.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eresolution args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.resolution)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eresolution args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eresolution.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.resolution ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eresolution t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.resolution) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eresolution t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eresolution (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_resolution hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.chain_resolution`. -/
theorem CtorSpec.eo__24emb_5fr_2echain_5fresolution.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2echain_5fresolution args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.chain_resolution)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2echain_5fresolution args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2echain_5fresolution.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.chain_resolution ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2echain_5fresolution t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.chain_resolution) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2echain_5fresolution t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2echain_5fresolution (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_chain_resolution hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.chain_m_resolution`. -/
theorem CtorSpec.eo__24emb_5fr_2echain_5fm_5fresolution.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.chain_m_resolution)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2echain_5fm_5fresolution.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.chain_m_resolution ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.chain_m_resolution) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2echain_5fm_5fresolution (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_chain_m_resolution hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.factoring`. -/
theorem CtorSpec.eo__24emb_5fr_2efactoring.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2efactoring args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.factoring)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2efactoring args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2efactoring.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.factoring ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2efactoring t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.factoring) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2efactoring t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2efactoring (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_factoring hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.reordering`. -/
theorem CtorSpec.eo__24emb_5fr_2ereordering.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ereordering args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.reordering)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ereordering args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ereordering.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.reordering ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ereordering t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.reordering) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ereordering t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ereordering (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_reordering hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.eq_resolve`. -/
theorem CtorSpec.eo__24emb_5fr_2eeq_5fresolve.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eeq_5fresolve args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.eq_resolve)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eeq_5fresolve args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eeq_5fresolve.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.eq_resolve ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fresolve t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.eq_resolve) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eeq_5fresolve t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eeq_5fresolve (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_eq_resolve hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.modus_ponens`. -/
theorem CtorSpec.eo__24emb_5fr_2emodus_5fponens.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2emodus_5fponens args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.modus_ponens)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2emodus_5fponens args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2emodus_5fponens.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.modus_ponens ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2emodus_5fponens t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.modus_ponens) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2emodus_5fponens t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2emodus_5fponens (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_modus_ponens hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_not_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fnot_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_not_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fnot_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_not_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_not_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fnot_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_not_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.contra`. -/
theorem CtorSpec.eo__24emb_5fr_2econtra.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econtra args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.contra)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econtra args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econtra.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.contra ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econtra t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.contra) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econtra t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econtra (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_contra hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.and_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2eand_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eand_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.and_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eand_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eand_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.and_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eand_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.and_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eand_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eand_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_and_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.and_intro`. -/
theorem CtorSpec.eo__24emb_5fr_2eand_5fintro.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eand_5fintro args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.and_intro)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eand_5fintro args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eand_5fintro.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.and_intro ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eand_5fintro t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.and_intro) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eand_5fintro t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eand_5fintro (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_and_intro hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_or_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5for_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5for_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_or_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5for_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5for_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_or_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5for_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_or_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5for_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5for_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_or_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.implies_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2eimplies_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eimplies_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.implies_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eimplies_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eimplies_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.implies_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eimplies_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.implies_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eimplies_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eimplies_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_implies_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_implies_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fimplies_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_implies_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fimplies_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_implies_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_implies_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_implies_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_implies_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fimplies_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_implies_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fimplies_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_implies_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_implies_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fimplies_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_implies_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.equiv_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2eequiv_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.equiv_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eequiv_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.equiv_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.equiv_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eequiv_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_equiv_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.equiv_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2eequiv_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.equiv_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eequiv_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.equiv_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.equiv_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eequiv_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_equiv_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_equiv_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fequiv_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_equiv_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fequiv_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_equiv_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_equiv_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_equiv_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_equiv_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fequiv_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_equiv_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fequiv_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_equiv_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_equiv_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fequiv_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_equiv_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.xor_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2exor_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2exor_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.xor_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2exor_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2exor_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.xor_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2exor_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.xor_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2exor_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2exor_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_xor_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.xor_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2exor_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2exor_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.xor_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2exor_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2exor_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.xor_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2exor_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.xor_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2exor_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2exor_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_xor_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_xor_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fxor_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_xor_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fxor_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_xor_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_xor_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_xor_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_xor_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fxor_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_xor_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fxor_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_xor_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_xor_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fxor_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_xor_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eite_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ite_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2eite_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eite_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ite_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eite_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eite_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ite_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ite_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eite_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eite_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ite_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_ite_elim1`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fite_5felim1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_ite_elim1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fite_5felim1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_ite_elim1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_ite_elim1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_ite_elim1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_ite_elim2`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fite_5felim2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_ite_elim2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fite_5felim2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_ite_elim2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_ite_elim2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fite_5felim2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_ite_elim2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.not_and`. -/
theorem CtorSpec.eo__24emb_5fr_2enot_5fand.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enot_5fand args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.not_and)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enot_5fand args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enot_5fand.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.not_and ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fand t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.not_and) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enot_5fand t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enot_5fand (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_not_and hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_and_pos`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fand_5fpos.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_and_pos)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fand_5fpos.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_and_pos ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_and_pos) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fpos (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_and_pos hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_and_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fand_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_and_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fand_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_and_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_and_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fand_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_and_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_or_pos`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5for_5fpos.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_or_pos)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5for_5fpos.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_or_pos ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_or_pos) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fpos (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_or_pos hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_or_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5for_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_or_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5for_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_or_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_or_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5for_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_or_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_implies_pos`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fimplies_5fpos.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_implies_pos)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fimplies_5fpos.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_implies_pos ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_implies_pos) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fpos (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_implies_pos hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_implies_neg1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fimplies_5fneg1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_implies_neg1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fimplies_5fneg1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_implies_neg1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_implies_neg1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_implies_neg1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_implies_neg2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fimplies_5fneg2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_implies_neg2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fimplies_5fneg2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_implies_neg2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_implies_neg2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fimplies_5fneg2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_implies_neg2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_equiv_pos1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fpos1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_equiv_pos1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fpos1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_equiv_pos1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_equiv_pos1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_equiv_pos1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_equiv_pos2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fpos2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_equiv_pos2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fpos2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_equiv_pos2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_equiv_pos2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fpos2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_equiv_pos2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_equiv_neg1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fneg1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_equiv_neg1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fneg1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_equiv_neg1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_equiv_neg1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_equiv_neg1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_equiv_neg2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fneg2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_equiv_neg2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fequiv_5fneg2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_equiv_neg2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_equiv_neg2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fequiv_5fneg2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_equiv_neg2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_xor_pos1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fpos1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_xor_pos1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fpos1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_xor_pos1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_xor_pos1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_xor_pos1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_xor_pos2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fpos2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_xor_pos2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fpos2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_xor_pos2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_xor_pos2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fpos2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_xor_pos2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_xor_neg1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fneg1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_xor_neg1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fneg1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_xor_neg1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_xor_neg1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_xor_neg1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_xor_neg2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fneg2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_xor_neg2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fxor_5fneg2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_xor_neg2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_xor_neg2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fxor_5fneg2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_xor_neg2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_ite_pos1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fpos1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_ite_pos1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fpos1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_ite_pos1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_ite_pos1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_ite_pos1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_ite_pos2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fpos2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_ite_pos2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fpos2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_ite_pos2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_ite_pos2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_ite_pos2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_ite_pos3`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fpos3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_ite_pos3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fpos3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_ite_pos3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_ite_pos3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fpos3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_ite_pos3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_ite_neg1`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fneg1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_ite_neg1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fneg1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_ite_neg1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_ite_neg1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_ite_neg1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_ite_neg2`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fneg2.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_ite_neg2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fneg2.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_ite_neg2 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_ite_neg2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg2 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_ite_neg2 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cnf_ite_neg3`. -/
theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fneg3.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cnf_ite_neg3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ecnf_5fite_5fneg3.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cnf_ite_neg3 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cnf_ite_neg3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ecnf_5fite_5fneg3 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cnf_ite_neg3 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arrays_read_over_write`. -/
theorem CtorSpec.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arrays_read_over_write)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arrays_read_over_write ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arrays_read_over_write) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arrays_read_over_write hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arrays_read_over_write_contra`. -/
theorem CtorSpec.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arrays_read_over_write_contra)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arrays_read_over_write_contra ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arrays_read_over_write_contra) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5fcontra (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arrays_read_over_write_contra hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arrays_read_over_write_1`. -/
theorem CtorSpec.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arrays_read_over_write_1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arrays_read_over_write_1 ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arrays_read_over_write_1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earrays_5fread_5fover_5fwrite_5f1 (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arrays_read_over_write_1 hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arrays_ext`. -/
theorem CtorSpec.eo__24emb_5fr_2earrays_5fext.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earrays_5fext args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arrays_ext)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earrays_5fext args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earrays_5fext.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arrays_ext ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fext t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arrays_ext) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earrays_5fext t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earrays_5fext (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arrays_ext hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.refl`. -/
theorem CtorSpec.eo__24emb_5fr_2erefl.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2erefl args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.refl)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2erefl args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2erefl.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.refl ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2erefl t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.refl) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2erefl t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2erefl (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_refl hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.symm`. -/
theorem CtorSpec.eo__24emb_5fr_2esymm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esymm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.symm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esymm args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esymm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.symm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esymm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.symm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esymm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esymm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_symm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.trans`. -/
theorem CtorSpec.eo__24emb_5fr_2etrans.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2etrans args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.trans)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2etrans args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2etrans.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.trans ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2etrans t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.trans) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2etrans t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2etrans (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_trans hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.cong`. -/
theorem CtorSpec.eo__24emb_5fr_2econg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.cong)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.cong ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.cong) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_cong hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.nary_cong`. -/
theorem CtorSpec.eo__24emb_5fr_2enary_5fcong.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2enary_5fcong args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.nary_cong)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2enary_5fcong args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2enary_5fcong.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.nary_cong ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enary_5fcong t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.nary_cong) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2enary_5fcong t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2enary_5fcong (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_nary_cong hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.pairwise_cong`. -/
theorem CtorSpec.eo__24emb_5fr_2epairwise_5fcong.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2epairwise_5fcong args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.pairwise_cong)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2epairwise_5fcong args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2epairwise_5fcong.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.pairwise_cong ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2epairwise_5fcong t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.pairwise_cong) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2epairwise_5fcong t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2epairwise_5fcong (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_pairwise_cong hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.true_intro`. -/
theorem CtorSpec.eo__24emb_5fr_2etrue_5fintro.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2etrue_5fintro args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.true_intro)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2etrue_5fintro args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2etrue_5fintro.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.true_intro ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2etrue_5fintro t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.true_intro) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2etrue_5fintro t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2etrue_5fintro (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_true_intro hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.true_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2etrue_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2etrue_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.true_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2etrue_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2etrue_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.true_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2etrue_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.true_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2etrue_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2etrue_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_true_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.false_intro`. -/
theorem CtorSpec.eo__24emb_5fr_2efalse_5fintro.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2efalse_5fintro args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.false_intro)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2efalse_5fintro args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2efalse_5fintro.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.false_intro ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2efalse_5fintro t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.false_intro) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2efalse_5fintro t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2efalse_5fintro (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_false_intro hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.false_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2efalse_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2efalse_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.false_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2efalse_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2efalse_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.false_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2efalse_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.false_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2efalse_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2efalse_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_false_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ho_cong`. -/
theorem CtorSpec.eo__24emb_5fr_2eho_5fcong.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eho_5fcong args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ho_cong)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eho_5fcong args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eho_5fcong.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ho_cong ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eho_5fcong t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ho_cong) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eho_5fcong t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eho_5fcong (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ho_cong hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.distinct_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2edistinct_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edistinct_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.distinct_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edistinct_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2edistinct_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.distinct_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.distinct_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edistinct_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_distinct_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.distinct_true`. -/
theorem CtorSpec.eo__24emb_5fr_2edistinct_5ftrue.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.distinct_true)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2edistinct_5ftrue.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.distinct_true ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.distinct_true) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edistinct_5ftrue (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_distinct_true hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.distinct_false`. -/
theorem CtorSpec.eo__24emb_5fr_2edistinct_5ffalse.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.distinct_false)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2edistinct_5ffalse.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.distinct_false ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.distinct_false) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2edistinct_5ffalse (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_distinct_false hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_sum_ub`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fsum_5fub.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_sum_ub)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fsum_5fub.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_sum_ub ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_sum_ub) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fsum_5fub (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_sum_ub hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mult_pos`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fpos.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mult_pos)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fpos.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mult_pos ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mult_pos) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fpos (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mult_pos hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mult_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mult_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mult_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mult_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mult_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_trichotomy`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5ftrichotomy.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_trichotomy)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5ftrichotomy.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_trichotomy ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_trichotomy) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5ftrichotomy (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_trichotomy hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.int_tight_ub`. -/
theorem CtorSpec.eo__24emb_5fr_2eint_5ftight_5fub.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.int_tight_ub)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eint_5ftight_5fub.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.int_tight_ub ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.int_tight_ub) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eint_5ftight_5fub (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_int_tight_ub hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.int_tight_lb`. -/
theorem CtorSpec.eo__24emb_5fr_2eint_5ftight_5flb.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.int_tight_lb)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eint_5ftight_5flb.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.int_tight_lb ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.int_tight_lb) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eint_5ftight_5flb (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_int_tight_lb hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mult_tangent`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5ftangent.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mult_tangent)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5ftangent.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mult_tangent ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mult_tangent) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmult_5ftangent (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mult_tangent hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mult_sign`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fsign.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mult_sign)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fsign.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mult_sign ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mult_sign) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fsign (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mult_sign hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_mult_abs_comparison`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_mult_abs_comparison)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_mult_abs_comparison ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_mult_abs_comparison) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fmult_5fabs_5fcomparison (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_mult_abs_comparison hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_reduction`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5freduction.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5freduction args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_reduction)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5freduction args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5freduction.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_reduction ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5freduction t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_reduction) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5freduction t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5freduction (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_reduction hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_poly_norm`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fpoly_5fnorm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_poly_norm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fpoly_5fnorm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_poly_norm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_poly_norm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_poly_norm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_poly_norm_rel`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_poly_norm_rel)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_poly_norm_rel ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_poly_norm_rel) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fpoly_5fnorm_5frel (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_poly_norm_rel hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_repeat_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5frepeat_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_repeat_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5frepeat_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_repeat_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_repeat_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5frepeat_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_repeat_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_smulo_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fsmulo_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_smulo_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fsmulo_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_smulo_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_smulo_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fsmulo_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_smulo_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_umulo_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fumulo_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_umulo_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fumulo_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_umulo_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_umulo_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fumulo_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_umulo_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_bitwise_slicing`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fbitwise_5fslicing.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_bitwise_slicing)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fbitwise_5fslicing.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_bitwise_slicing ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_bitwise_slicing) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fbitwise_5fslicing (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_bitwise_slicing hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_bitblast_step`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fbitblast_5fstep.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_bitblast_step)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fbitblast_5fstep.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_bitblast_step ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_bitblast_step) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fbitblast_5fstep (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_bitblast_step hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_poly_norm`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fpoly_5fnorm.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_poly_norm)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fpoly_5fnorm.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_poly_norm ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_poly_norm) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_poly_norm hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.bv_poly_norm_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.bv_poly_norm_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.bv_poly_norm_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.bv_poly_norm_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ebv_5fpoly_5fnorm_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_bv_poly_norm_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_length_pos`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5flength_5fpos.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_length_pos)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5flength_5fpos.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_length_pos ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_length_pos) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5flength_5fpos (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_length_pos hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_length_non_empty`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5flength_5fnon_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_length_non_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5flength_5fnon_5fempty.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_length_non_empty ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_length_non_empty) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5flength_5fnon_5fempty (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_length_non_empty hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.concat_eq`. -/
theorem CtorSpec.eo__24emb_5fr_2econcat_5feq.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econcat_5feq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.concat_eq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econcat_5feq args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econcat_5feq.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.concat_eq ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5feq t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.concat_eq) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5feq t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econcat_5feq (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_concat_eq hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.concat_unify`. -/
theorem CtorSpec.eo__24emb_5fr_2econcat_5funify.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econcat_5funify args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.concat_unify)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econcat_5funify args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econcat_5funify.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.concat_unify ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5funify t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.concat_unify) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5funify t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econcat_5funify (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_concat_unify hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.concat_csplit`. -/
theorem CtorSpec.eo__24emb_5fr_2econcat_5fcsplit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.concat_csplit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econcat_5fcsplit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.concat_csplit ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.concat_csplit) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econcat_5fcsplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_concat_csplit hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.concat_split`. -/
theorem CtorSpec.eo__24emb_5fr_2econcat_5fsplit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econcat_5fsplit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.concat_split)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econcat_5fsplit args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econcat_5fsplit.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.concat_split ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5fsplit t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.concat_split) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5fsplit t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econcat_5fsplit (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_concat_split hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.concat_lprop`. -/
theorem CtorSpec.eo__24emb_5fr_2econcat_5flprop.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econcat_5flprop args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.concat_lprop)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econcat_5flprop args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econcat_5flprop.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.concat_lprop ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5flprop t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.concat_lprop) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5flprop t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econcat_5flprop (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_concat_lprop hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.concat_cprop`. -/
theorem CtorSpec.eo__24emb_5fr_2econcat_5fcprop.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2econcat_5fcprop args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.concat_cprop)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2econcat_5fcprop args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2econcat_5fcprop.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.concat_cprop ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5fcprop t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.concat_cprop) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2econcat_5fcprop t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2econcat_5fcprop (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_concat_cprop hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_decompose`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5fdecompose.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5fdecompose args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_decompose)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5fdecompose args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5fdecompose.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_decompose ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fdecompose t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_decompose) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fdecompose t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5fdecompose (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_decompose hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.exists_string_length`. -/
theorem CtorSpec.eo__24emb_5fr_2eexists_5fstring_5flength.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.exists_string_length)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eexists_5fstring_5flength.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.exists_string_length ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.exists_string_length) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eexists_5fstring_5flength (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_exists_string_length hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_code_inj`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5fcode_5finj.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_code_inj)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5fcode_5finj.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_code_inj ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_code_inj) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5fcode_5finj (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_code_inj hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_seq_unit_inj`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5fseq_5funit_5finj.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_seq_unit_inj)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5fseq_5funit_5finj.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_seq_unit_inj ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_seq_unit_inj) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5fseq_5funit_5finj (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_seq_unit_inj hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_inter`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5finter.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5finter args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_inter)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5finter args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5finter.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_inter ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_inter) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5finter (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_inter hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_concat`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5fconcat args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5fconcat.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_concat ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_concat) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5fconcat t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5fconcat (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_concat hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_unfold_pos`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5funfold_5fpos.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_unfold_pos)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5funfold_5fpos.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_unfold_pos ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_unfold_pos) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fpos (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_unfold_pos hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_unfold_neg_concat_fixed`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_unfold_neg_concat_fixed)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_unfold_neg_concat_fixed ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_unfold_neg_concat_fixed) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_unfold_neg_concat_fixed hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_unfold_neg`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5funfold_5fneg.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_unfold_neg)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5funfold_5fneg.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_unfold_neg ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_unfold_neg) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5funfold_5fneg (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_unfold_neg hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_ext`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5fext.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5fext args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_ext)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5fext args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5fext.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_ext ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fext t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_ext) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5fext t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5fext (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_ext hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_reduction`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5freduction.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5freduction args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_reduction)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5freduction args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5freduction.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_reduction ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5freduction t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_reduction) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5freduction t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5freduction (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_reduction hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.string_eager_reduction`. -/
theorem CtorSpec.eo__24emb_5fr_2estring_5feager_5freduction.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.string_eager_reduction)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estring_5feager_5freduction.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.string_eager_reduction ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.string_eager_reduction) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estring_5feager_5freduction (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_string_eager_reduction hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_string_pred_entail`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_string_pred_entail)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_string_pred_entail ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_string_pred_entail) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fentail (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_string_pred_entail hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.arith_string_pred_safe_approx`. -/
theorem CtorSpec.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.arith_string_pred_safe_approx)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.arith_string_pred_safe_approx ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.arith_string_pred_safe_approx) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_arith_string_pred_safe_approx hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_eval`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5feval.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_eval)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5feval.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_eval ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_eval) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5feval (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_eval hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_consume`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fconsume.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_consume)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fconsume.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_consume ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_consume) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconsume (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_consume hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_loop_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5floop_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_loop_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5floop_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_loop_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_loop_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5floop_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_loop_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_eq_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5feq_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_eq_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5feq_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_eq_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_eq_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5feq_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_eq_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_inter_inclusion`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5finclusion.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_inter_inclusion)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5finter_5finclusion.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_inter_inclusion ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_inter_inclusion) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5finter_5finclusion (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_inter_inclusion hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.re_union_inclusion`. -/
theorem CtorSpec.eo__24emb_5fr_2ere_5funion_5finclusion.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.re_union_inclusion)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2ere_5funion_5finclusion.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.re_union_inclusion ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.re_union_inclusion) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2ere_5funion_5finclusion (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_re_union_inclusion hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_concat_star_char`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_concat_star_char)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_concat_star_char ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_concat_star_char) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_concat_star_char hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_sigma`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fsigma.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_sigma)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fsigma.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_sigma ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_sigma) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_sigma hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_in_re_sigma_star`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_in_re_sigma_star)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_in_re_sigma_star ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_in_re_sigma_star) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_in_re_sigma_star hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_ctn_multiset_subset`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_ctn_multiset_subset)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_ctn_multiset_subset ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_ctn_multiset_subset) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_ctn_multiset_subset hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_overlap_split_ctn`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_overlap_split_ctn)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_overlap_split_ctn ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_overlap_split_ctn) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_overlap_split_ctn hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_overlap_endpoints_ctn`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_overlap_endpoints_ctn)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_overlap_endpoints_ctn ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_overlap_endpoints_ctn) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_overlap_endpoints_ctn hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_overlap_endpoints_indexof`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_overlap_endpoints_indexof)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_overlap_endpoints_indexof ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_overlap_endpoints_indexof) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_overlap_endpoints_indexof hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_overlap_endpoints_replace`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_overlap_endpoints_replace)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_overlap_endpoints_replace ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_overlap_endpoints_replace) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_overlap_endpoints_replace hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_indexof_re_eval`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fre_5feval.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_indexof_re_eval)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5findexof_5fre_5feval.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_indexof_re_eval ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_indexof_re_eval) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5findexof_5fre_5feval (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_indexof_re_eval hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_re_eval`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5feval.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_re_eval)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5feval.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_re_eval ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_re_eval) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5feval (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_re_eval hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.str_replace_re_all_eval`. -/
theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.str_replace_re_all_eval)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.str_replace_re_all_eval ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.str_replace_re_all_eval) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_str_replace_re_all_eval hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.seq_eval_op`. -/
theorem CtorSpec.eo__24emb_5fr_2eseq_5feval_5fop.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.seq_eval_op)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eseq_5feval_5fop.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.seq_eval_op ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.seq_eval_op) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eseq_5feval_5fop (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_seq_eval_op hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_singleton_inj`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fsingleton_5finj.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_singleton_inj)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fsingleton_5finj.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_singleton_inj ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_singleton_inj) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fsingleton_5finj (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_singleton_inj hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_ext`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fext.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fext args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_ext)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fext args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fext.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_ext ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fext t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_ext) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fext t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fext (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_ext hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_choose_member`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5fchoose_5fmember.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_choose_member)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5fchoose_5fmember.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_choose_member ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_choose_member) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5fchoose_5fmember (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_choose_member hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.sets_eval_op`. -/
theorem CtorSpec.eo__24emb_5fr_2esets_5feval_5fop.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.sets_eval_op)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2esets_5feval_5fop.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.sets_eval_op ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.sets_eval_op) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2esets_5feval_5fop (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_sets_eval_op hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ubv_to_int_range`. -/
theorem CtorSpec.eo__24emb_5fr_2eubv_5fto_5fint_5frange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ubv_to_int_range)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eubv_5fto_5fint_5frange.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ubv_to_int_range ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ubv_to_int_range) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5frange (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ubv_to_int_range hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.ubv_to_int_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2eubv_5fto_5fint_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.ubv_to_int_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eubv_5fto_5fint_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.ubv_to_int_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.ubv_to_int_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eubv_5fto_5fint_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_ubv_to_int_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.int_to_bv_elim`. -/
theorem CtorSpec.eo__24emb_5fr_2eint_5fto_5fbv_5felim.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.int_to_bv_elim)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eint_5fto_5fbv_5felim.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.int_to_bv_elim ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.int_to_bv_elim) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eint_5fto_5fbv_5felim (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_int_to_bv_elim hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.instantiate`. -/
theorem CtorSpec.eo__24emb_5fr_2einstantiate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2einstantiate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.instantiate)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2einstantiate args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2einstantiate.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.instantiate ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2einstantiate t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.instantiate) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2einstantiate t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2einstantiate (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_instantiate hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.skolemize`. -/
theorem CtorSpec.eo__24emb_5fr_2eskolemize.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eskolemize args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.skolemize)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eskolemize args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eskolemize.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.skolemize ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eskolemize t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.skolemize) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eskolemize t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eskolemize (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_skolemize hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩

/-- `$emb_r.skolem_intro`. -/
theorem CtorSpec.eo__24emb_5fr_2eskolem_5fintro.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fr_2eskolem_5fintro args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.CRule.skolem_intro)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fr_2eskolem_5fintro args [] hinv h64 (.inl rfl)
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

theorem CtorSpec.eo__24emb_5fr_2eskolem_5fintro.destruct {s : Store} {t : Term} {x : Eo.CRule}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.CRule.skolem_intro ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eskolem_5fintro t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.CRule.skolem_intro) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fr_2eskolem_5fintro t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fr_2eskolem_5fintro (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_skolem_intro hx h.2
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_CRule, Embed.enc_CRule]), hd⟩


end pathos_compiled_checker
