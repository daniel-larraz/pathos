module

public import MiniChecker
public import PathosProofs.Runtime.Node
public import MiniEmbed

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
`MiniCtors.lean`); `MiniChecker` is the Lean of the compiled checker.
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CArgList_nil hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CArgList_cons hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CCmd_assume_push hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CCmd_check_proven hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_CCmd_step hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_CCmd_step_pop hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CCmdList_nil hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CCmdList_cons hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CIndexList_nil hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CIndexList_cons hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_scope hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_contra hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_refl hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_symm hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CRule_trans hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CState_nil hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_CState_Stuck hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_CState_cons hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CStateObj_assume hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CStateObj_assume_push hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_CStateObj_proven hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Datatype_null hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Datatype_sum hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_DatatypeCons_unit hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_DatatypeCons_cons hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_DatatypeDecl_nil hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_DatatypeDecl_cons hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_Proof_pf hx
    have he := h.2
    simp only [Embed.embedded_emb_Proof, Embed.emb_Proof] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_Proof, Embed.enc_Proof]), hd⟩

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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtDatatype_null hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtDatatype_sum hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtDatatypeCons_unit hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtDatatypeCons_cons hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtDatatypeDecl_nil hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtDatatypeDecl_cons hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtTerm_None hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_Boolean hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_Numeral hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_Rational hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_String hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_Binary hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_Apply hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_Var hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_DtCons hx
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
  · obtain ⟨x0, x1, x2, x3, rfl, rfl⟩ := Embed.inv_SmtTerm_DtSel hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_DtTester hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_UConst hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtTerm_not hx
    have he := h.2
    simp only [Embed.embedded_emb_SmtTerm, Embed.emb_SmtTerm] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_and hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_or hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_imp hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtTerm_eq hx
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_SmtTerm_ite hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_None hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Bool hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Int hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Real hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_RegLan hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_BitVec hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_Map hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_Set hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_Seq hx
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_SmtType_Char hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_Datatype hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_TypeRef hx
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_SmtType_USort hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_FunType hx
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_SmtType_DtcAppType hx
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

/-- `$eo_List`. -/
theorem CtorSpec.eo__24eo_5fList.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24eo_5fList args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.__eo_List)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24eo_5fList args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

theorem CtorSpec.eo__24eo_5fList.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Term.__eo_List ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24eo_5fList t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Term.__eo_List) ∧
      Store.destruct s schema.Constructor.eo__24eo_5fList t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24eo_5fList (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term___eo_List hx
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$eo_List_nil`. -/
theorem CtorSpec.eo__24eo_5fList_5fnil.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24eo_5fList_5fnil args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.__eo_List_nil)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24eo_5fList_5fnil args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

theorem CtorSpec.eo__24eo_5fList_5fnil.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Term.__eo_List_nil ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24eo_5fList_5fnil t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Term.__eo_List_nil) ∧
      Store.destruct s schema.Constructor.eo__24eo_5fList_5fnil t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24eo_5fList_5fnil (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term___eo_List_nil hx
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$eo_List_cons`. -/
theorem CtorSpec.eo__24eo_5fList_5fcons.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24eo_5fList_5fcons args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.__eo_List_cons)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24eo_5fList_5fcons args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

theorem CtorSpec.eo__24eo_5fList_5fcons.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Term.__eo_List_cons ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24eo_5fList_5fcons t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Term.__eo_List_cons) ∧
      Store.destruct s schema.Constructor.eo__24eo_5fList_5fcons t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24eo_5fList_5fcons (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term___eo_List_cons hx
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_Bool`. -/
theorem CtorSpec.eo__24emb_5fBool.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fBool args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.Bool)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fBool args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

theorem CtorSpec.eo__24emb_5fBool.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Term.Bool ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fBool t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Term.Bool) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fBool t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fBool (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term_Bool hx
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_Type`. -/
theorem CtorSpec.eo__24emb_5fType.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fType args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.Type)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fType args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

theorem CtorSpec.eo__24emb_5fType.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Term.Type ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fType t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Term.Type) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fType t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fType (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term_Type hx
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_FunType`. -/
theorem CtorSpec.eo__24emb_5fFunType.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fFunType args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.FunType)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fFunType args [] hinv h64 (.inl rfl)
    (by rw [hargs]; exact HoldsList.nil))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp [Embed.embedded_emb_Term, Embed.emb_Term]

theorem CtorSpec.eo__24emb_5fFunType.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (v : alloc.vec.Vec Term), x = Eo.Term.FunType ∧ v.val = [] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fFunType t = ok (core.result.Result.Ok (some v), s)) ∨
    ((x ≠ Eo.Term.FunType) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fFunType t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fFunType (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term_FunType hx
    generalize hvl : v.val = l at hl
    cases hl
    exact Or.inl ⟨v, rfl, hvl, hd⟩
  · exact Or.inr ⟨fun he => hne []
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_Var`. -/
theorem CtorSpec.eo__24emb_5fVar.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term} {a1 : Term} {x1 : Eo.Term}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fVar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.Var x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fVar args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inr rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fVar.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term) (x1 : Eo.Term), x = Eo.Term.Var x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fVar t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term) (x1 : Eo.Term), x ≠ Eo.Term.Var x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fVar t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fVar (.inr rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_Var hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_DatatypeType`. -/
theorem CtorSpec.eo__24emb_5fDatatypeType.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Eo.DatatypeDecl}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fDatatypeType args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.DatatypeType x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fDatatypeType args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fDatatypeType.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Eo.DatatypeDecl), x = Eo.Term.DatatypeType x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDatatypeType t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Eo.DatatypeDecl), x ≠ Eo.Term.DatatypeType x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDatatypeType t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fDatatypeType (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_DatatypeType hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_DatatypeTypeRef`. -/
theorem CtorSpec.eo__24emb_5fDatatypeTypeRef.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fDatatypeTypeRef args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.DatatypeTypeRef x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fDatatypeTypeRef args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact h0.2

theorem CtorSpec.eo__24emb_5fDatatypeTypeRef.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String), x = Eo.Term.DatatypeTypeRef x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDatatypeTypeRef t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String), x ≠ Eo.Term.DatatypeTypeRef x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDatatypeTypeRef t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fDatatypeTypeRef (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_Term_DatatypeTypeRef hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_DtcAppType`. -/
theorem CtorSpec.eo__24emb_5fDtcAppType.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : Eo.Term} {a1 : Term} {x1 : Eo.Term}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fDtcAppType args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.DtcAppType x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fDtcAppType args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fDtcAppType.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : Eo.Term) (x1 : Eo.Term), x = Eo.Term.DtcAppType x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDtcAppType t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : Eo.Term) (x1 : Eo.Term), x ≠ Eo.Term.DtcAppType x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDtcAppType t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fDtcAppType (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_DtcAppType hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_DtCons`. -/
theorem CtorSpec.eo__24emb_5fDtCons.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Eo.DatatypeDecl} {a2 : Term} {x2 : SmtEval.native_Nat}
    (hargs : args.val = [a0, a1, a2]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fDtCons args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.DtCons x0 x1 x2)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fDtCons args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 HoldsList.nil)))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact ⟨h0.2, h1.2, h2.2⟩

theorem CtorSpec.eo__24emb_5fDtCons.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Eo.DatatypeDecl) (x2 : SmtEval.native_Nat), x = Eo.Term.DtCons x0 x1 x2 ∧ v.val = [f0, f1, f2] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDtCons t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Eo.DatatypeDecl) (x2 : SmtEval.native_Nat), x ≠ Eo.Term.DtCons x0 x1 x2) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDtCons t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fDtCons (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_Term_DtCons hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
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
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_DtSel`. -/
theorem CtorSpec.eo__24emb_5fDtSel.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_String} {a1 : Term} {x1 : Eo.DatatypeDecl} {a2 : Term} {x2 : SmtEval.native_Nat} {a3 : Term} {x3 : SmtEval.native_Nat}
    (hargs : args.val = [a0, a1, a2, a3]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (h2 : Represents.rep s a2 x2) (h3 : Represents.rep s a3 x3) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fDtSel args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.DtSel x0 x1 x2 x3)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fDtSel args [Embedded.enc x0, Embedded.enc x1, Embedded.enc x2, Embedded.enc x3] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 (HoldsList.cons _ _ _ _ h2.1 (HoldsList.cons _ _ _ _ h3.1 HoldsList.nil))))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact ⟨h0.2, h1.2, h2.2, h3.2⟩

theorem CtorSpec.eo__24emb_5fDtSel.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (f2 : Term) (f3 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_String) (x1 : Eo.DatatypeDecl) (x2 : SmtEval.native_Nat) (x3 : SmtEval.native_Nat), x = Eo.Term.DtSel x0 x1 x2 x3 ∧ v.val = [f0, f1, f2, f3] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧ Represents.rep s f2 x2 ∧ Represents.rep s f3 x3 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDtSel t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_String) (x1 : Eo.DatatypeDecl) (x2 : SmtEval.native_Nat) (x3 : SmtEval.native_Nat), x ≠ Eo.Term.DtSel x0 x1 x2 x3) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fDtSel t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fDtSel (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, x2, x3, rfl, rfl⟩ := Embed.inv_Term_DtSel hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
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
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_USort`. -/
theorem CtorSpec.eo__24emb_5fUSort.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Nat}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fUSort args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.USort x0)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fUSort args [Embedded.enc x0] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 HoldsList.nil)))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact h0.2

theorem CtorSpec.eo__24emb_5fUSort.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Nat), x = Eo.Term.USort x0 ∧ v.val = [f0] ∧ Represents.rep s f0 x0 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fUSort t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Nat), x ≠ Eo.Term.USort x0) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fUSort t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fUSort (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_Term_USort hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact Or.inl ⟨f0, v, x0, rfl, hvl, ⟨h0, he⟩, hd⟩
  · exact Or.inr ⟨fun x0 he => hne [Embedded.enc x0]
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩

/-- `$emb_UConst`. -/
theorem CtorSpec.eo__24emb_5fUConst.construct (s : Store) (args : Slice Term) {a0 : Term} {x0 : SmtEval.native_Nat} {a1 : Term} {x1 : Eo.Term}
    (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 x0) (h1 : Represents.rep s a1 x1) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fUConst args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UConst x0 x1)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__24emb_5fUConst args [Embedded.enc x0, Embedded.enc x1] hinv h64 (.inl rfl)
    (by rw [hargs]; exact (HoldsList.cons _ _ _ _ h0.1 (HoldsList.cons _ _ _ _ h1.1 HoldsList.nil))))
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  simp only [WP.uncurry'_pair] at hr ⊢
  refine ⟨hinv', hg, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, ?_⟩
    · simpa [Embed.embedded_enc_Term, Embed.enc_Term] using hr
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term]
      exact ⟨h0.2, h1.2⟩

theorem CtorSpec.eo__24emb_5fUConst.destruct {s : Store} {t : Term} {x : Eo.Term}
    (h : Represents.rep s t x) :
    (∃ (f0 : Term) (f1 : Term) (v : alloc.vec.Vec Term) (x0 : SmtEval.native_Nat) (x1 : Eo.Term), x = Eo.Term.UConst x0 x1 ∧ v.val = [f0, f1] ∧ Represents.rep s f0 x0 ∧ Represents.rep s f1 x1 ∧
      Store.destruct s schema.Constructor.eo__24emb_5fUConst t = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ (x0 : SmtEval.native_Nat) (x1 : Eo.Term), x ≠ Eo.Term.UConst x0 x1) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fUConst t = ok (core.result.Result.Ok none, s)) := by
  rcases Store.destruct_holds schema.Constructor.eo__24emb_5fUConst (.inl rfl) h.1 with
    ⟨v, xs, hx, hl, hd⟩ | ⟨hne, hd⟩
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_UConst hx
    have he := h.2
    simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
    generalize hvl : v.val = l at hl
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        exact Or.inl ⟨f0, f1, v, x0, x1, rfl, hvl, ⟨h0, he.1⟩, ⟨h1, he.2⟩, hd⟩
  · exact Or.inr ⟨fun x0 x1 he => hne [Embedded.enc x0, Embedded.enc x1]
      (by subst he; simp [Embed.embedded_enc_Term, Embed.enc_Term]), hd⟩


end pathos_compiled_checker
