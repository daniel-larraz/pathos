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

/-- The user operator `bvredor`. -/
theorem CtorSpec.eo_bvredor.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_bvredor args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.bvredor)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_bvredor args [] hinv h64 (.inl rfl)
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

/-- The user operator `@from_bools`. -/
theorem CtorSpec.eo__40from_5fbools.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40from_5fbools args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_from_bools)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40from_5fbools args [] hinv h64 (.inl rfl)
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

/-- The user operator `RegLan`. -/
theorem CtorSpec.eo_RegLan.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_RegLan args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.RegLan)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_RegLan args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.len`. -/
theorem CtorSpec.eo_str_2elen.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2elen args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_len)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2elen args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.++`. -/
theorem CtorSpec.eo_str_2e_2b_2b.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2e_2b_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2e_2b_2b args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.substr`. -/
theorem CtorSpec.eo_str_2esubstr.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2esubstr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_substr)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2esubstr args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.contains`. -/
theorem CtorSpec.eo_str_2econtains.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2econtains args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_contains)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2econtains args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.replace`. -/
theorem CtorSpec.eo_str_2ereplace.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2ereplace args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_replace)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2ereplace args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.indexof`. -/
theorem CtorSpec.eo_str_2eindexof.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eindexof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_indexof)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eindexof args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.at`. -/
theorem CtorSpec.eo_str_2eat.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eat args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_at)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eat args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.prefixof`. -/
theorem CtorSpec.eo_str_2eprefixof.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eprefixof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_prefixof)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eprefixof args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.suffixof`. -/
theorem CtorSpec.eo_str_2esuffixof.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2esuffixof args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_suffixof)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2esuffixof args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.rev`. -/
theorem CtorSpec.eo_str_2erev.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2erev args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_rev)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2erev args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.update`. -/
theorem CtorSpec.eo_str_2eupdate.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eupdate args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_update)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eupdate args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.to_lower`. -/
theorem CtorSpec.eo_str_2eto_5flower.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eto_5flower args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_to_lower)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eto_5flower args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.to_upper`. -/
theorem CtorSpec.eo_str_2eto_5fupper.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eto_5fupper args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_to_upper)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eto_5fupper args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.to_code`. -/
theorem CtorSpec.eo_str_2eto_5fcode.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eto_5fcode args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_to_code)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eto_5fcode args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.from_code`. -/
theorem CtorSpec.eo_str_2efrom_5fcode.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2efrom_5fcode args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_from_code)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2efrom_5fcode args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.is_digit`. -/
theorem CtorSpec.eo_str_2eis_5fdigit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eis_5fdigit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_is_digit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eis_5fdigit args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.to_int`. -/
theorem CtorSpec.eo_str_2eto_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_to_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eto_5fint args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.from_int`. -/
theorem CtorSpec.eo_str_2efrom_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2efrom_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_from_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2efrom_5fint args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.<`. -/
theorem CtorSpec.eo_str_2e_3c.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2e_3c args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_lt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2e_3c args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.<=`. -/
theorem CtorSpec.eo_str_2e_3c_3d.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2e_3c_3d args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_leq)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2e_3c_3d args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.replace_all`. -/
theorem CtorSpec.eo_str_2ereplace_5fall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2ereplace_5fall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_replace_all)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2ereplace_5fall args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.replace_re`. -/
theorem CtorSpec.eo_str_2ereplace_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2ereplace_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_replace_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2ereplace_5fre args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.replace_re_all`. -/
theorem CtorSpec.eo_str_2ereplace_5fre_5fall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2ereplace_5fre_5fall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_replace_re_all)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2ereplace_5fre_5fall args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.indexof_re`. -/
theorem CtorSpec.eo_str_2eindexof_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eindexof_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_indexof_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eindexof_5fre args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.allchar`. -/
theorem CtorSpec.eo_re_2eallchar.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2eallchar args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_allchar)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2eallchar args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.none`. -/
theorem CtorSpec.eo_re_2enone.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2enone args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_none)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2enone args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.all`. -/
theorem CtorSpec.eo_re_2eall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2eall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_all)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2eall args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.to_re`. -/
theorem CtorSpec.eo_str_2eto_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2eto_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_to_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2eto_5fre args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.*`. -/
theorem CtorSpec.eo_re_2e_2a.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2e_2a args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_mult)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2e_2a args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.+`. -/
theorem CtorSpec.eo_re_2e_2b.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2e_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_plus)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2e_2b args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.opt`. -/
theorem CtorSpec.eo_re_2eopt.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2eopt args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_opt)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2eopt args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.comp`. -/
theorem CtorSpec.eo_re_2ecomp.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2ecomp args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_comp)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2ecomp args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.range`. -/
theorem CtorSpec.eo_re_2erange.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2erange args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_range)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2erange args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.++`. -/
theorem CtorSpec.eo_re_2e_2b_2b.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2e_2b_2b args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_concat)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2e_2b_2b args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.inter`. -/
theorem CtorSpec.eo_re_2einter.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2einter args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_inter)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2einter args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.union`. -/
theorem CtorSpec.eo_re_2eunion.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2eunion args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_union)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2eunion args [] hinv h64 (.inl rfl)
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

/-- The user operator `re.diff`. -/
theorem CtorSpec.eo_re_2ediff.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_re_2ediff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.re_diff)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_re_2ediff args [] hinv h64 (.inl rfl)
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

/-- The user operator `str.in_re`. -/
theorem CtorSpec.eo_str_2ein_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_str_2ein_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.str_in_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_str_2ein_5fre args [] hinv h64 (.inl rfl)
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

/-- The user operator `seq.unit`. -/
theorem CtorSpec.eo_seq_2eunit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_seq_2eunit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.seq_unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_seq_2eunit args [] hinv h64 (.inl rfl)
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

/-- The user operator `seq.nth`. -/
theorem CtorSpec.eo_seq_2enth.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_seq_2enth args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.seq_nth)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_seq_2enth args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_deq_diff`. -/
theorem CtorSpec.eo__40strings_5fdeq_5fdiff.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5fdeq_5fdiff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_deq_diff)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5fdeq_5fdiff args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_stoi_result`. -/
theorem CtorSpec.eo__40strings_5fstoi_5fresult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5fstoi_5fresult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_stoi_result)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5fstoi_5fresult args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_stoi_non_digit`. -/
theorem CtorSpec.eo__40strings_5fstoi_5fnon_5fdigit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5fstoi_5fnon_5fdigit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_stoi_non_digit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5fstoi_5fnon_5fdigit args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_itos_result`. -/
theorem CtorSpec.eo__40strings_5fitos_5fresult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5fitos_5fresult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_itos_result)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5fitos_5fresult args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_num_occur`. -/
theorem CtorSpec.eo__40strings_5fnum_5foccur.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5fnum_5foccur args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_num_occur)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5fnum_5foccur args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_num_occur_re`. -/
theorem CtorSpec.eo__40strings_5fnum_5foccur_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5fnum_5foccur_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_num_occur_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5fnum_5foccur_5fre args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_occur_index`. -/
theorem CtorSpec.eo__40strings_5foccur_5findex.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5foccur_5findex args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_occur_index)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5foccur_5findex args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_occur_index_re`. -/
theorem CtorSpec.eo__40strings_5foccur_5findex_5fre.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5foccur_5findex_5fre args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_occur_index_re)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5foccur_5findex_5fre args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_replace_all_result`. -/
theorem CtorSpec.eo__40strings_5freplace_5fall_5fresult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5freplace_5fall_5fresult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_replace_all_result)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5freplace_5fall_5fresult args [] hinv h64 (.inl rfl)
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

/-- The user operator `@strings_replace_re_all_result`. -/
theorem CtorSpec.eo__40strings_5freplace_5fre_5fall_5fresult.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40strings_5freplace_5fre_5fall_5fresult args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_strings_replace_re_all_result)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40strings_5freplace_5fre_5fall_5fresult args [] hinv h64 (.inl rfl)
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

/-- The user operator `UnitTuple`. -/
theorem CtorSpec.eo_UnitTuple.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_UnitTuple args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.UnitTuple)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_UnitTuple args [] hinv h64 (.inl rfl)
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

/-- The user operator `Tuple`. -/
theorem CtorSpec.eo_Tuple.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Tuple args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Tuple)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Tuple args [] hinv h64 (.inl rfl)
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

/-- The user operator `tuple.unit`. -/
theorem CtorSpec.eo_tuple_2eunit.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_tuple_2eunit args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.tuple_unit)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_tuple_2eunit args [] hinv h64 (.inl rfl)
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

/-- The user operator `tuple`. -/
theorem CtorSpec.eo_tuple.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_tuple args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.tuple)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_tuple args [] hinv h64 (.inl rfl)
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

/-- The user operator `Set`. -/
theorem CtorSpec.eo_Set.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_Set args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.Set)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_Set args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.singleton`. -/
theorem CtorSpec.eo_set_2esingleton.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2esingleton args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_singleton)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2esingleton args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.union`. -/
theorem CtorSpec.eo_set_2eunion.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2eunion args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_union)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2eunion args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.inter`. -/
theorem CtorSpec.eo_set_2einter.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2einter args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_inter)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2einter args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.minus`. -/
theorem CtorSpec.eo_set_2eminus.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2eminus args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_minus)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2eminus args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.member`. -/
theorem CtorSpec.eo_set_2emember.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2emember args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_member)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2emember args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.subset`. -/
theorem CtorSpec.eo_set_2esubset.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2esubset args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_subset)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2esubset args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.choose`. -/
theorem CtorSpec.eo_set_2echoose.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2echoose args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_choose)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2echoose args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.is_empty`. -/
theorem CtorSpec.eo_set_2eis_5fempty.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2eis_5fempty args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_is_empty)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2eis_5fempty args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.is_singleton`. -/
theorem CtorSpec.eo_set_2eis_5fsingleton.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2eis_5fsingleton args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_is_singleton)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2eis_5fsingleton args [] hinv h64 (.inl rfl)
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

/-- The user operator `set.insert`. -/
theorem CtorSpec.eo_set_2einsert.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_set_2einsert args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.set_insert)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_set_2einsert args [] hinv h64 (.inl rfl)
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

/-- The user operator `@sets_deq_diff`. -/
theorem CtorSpec.eo__40sets_5fdeq_5fdiff.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40sets_5fdeq_5fdiff args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_sets_deq_diff)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40sets_5fdeq_5fdiff args [] hinv h64 (.inl rfl)
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

/-- The user operator `/`. -/
theorem CtorSpec.eo__2f.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__2f args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.qdiv)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__2f args [] hinv h64 (.inl rfl)
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

/-- The user operator `/_total`. -/
theorem CtorSpec.eo__2f_5ftotal.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__2f_5ftotal args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.qdiv_total)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__2f_5ftotal args [] hinv h64 (.inl rfl)
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

/-- The user operator `@div_by_zero`. -/
theorem CtorSpec.eo__40div_5fby_5fzero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40div_5fby_5fzero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at_div_by_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40div_5fby_5fzero args [] hinv h64 (.inl rfl)
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

/-- The user operator `@@Monomial`. -/
theorem CtorSpec.eo__40_40Monomial.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40Monomial args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_Monomial)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40Monomial args [] hinv h64 (.inl rfl)
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

/-- The user operator `@@mon`. -/
theorem CtorSpec.eo__40_40mon.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40mon args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_mon)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40mon args [] hinv h64 (.inl rfl)
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

/-- The user operator `@@Polynomial`. -/
theorem CtorSpec.eo__40_40Polynomial.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40Polynomial args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_Polynomial)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40Polynomial args [] hinv h64 (.inl rfl)
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

/-- The user operator `@@poly.zero`. -/
theorem CtorSpec.eo__40_40poly_2ezero.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40poly_2ezero args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_poly_zero)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40poly_2ezero args [] hinv h64 (.inl rfl)
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

/-- The user operator `@@poly`. -/
theorem CtorSpec.eo__40_40poly.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40poly args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_poly)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40poly args [] hinv h64 (.inl rfl)
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

/-- The user operator `forall`. -/
theorem CtorSpec.eo_forall.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_forall args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.forall)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_forall args [] hinv h64 (.inl rfl)
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

/-- The user operator `exists`. -/
theorem CtorSpec.eo_exists.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_exists args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.exists)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_exists args [] hinv h64 (.inl rfl)
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

/-- The user operator `ubv_to_int`. -/
theorem CtorSpec.eo_ubv_5fto_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_ubv_5fto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.ubv_to_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_ubv_5fto_5fint args [] hinv h64 (.inl rfl)
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

/-- The user operator `sbv_to_int`. -/
theorem CtorSpec.eo_sbv_5fto_5fint.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo_sbv_5fto_5fint args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp.sbv_to_int)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo_sbv_5fto_5fint args [] hinv h64 (.inl rfl)
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

/-- The user operator `@@aci_sorted`. -/
theorem CtorSpec.eo__40_40aci_5fsorted.construct (s : Store) (args : Slice Term)
    (hargs : args.val = []) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__40_40aci_5fsorted args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.UOp Eo.UserOp._at__at_aci_sorted)
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.construct_holds s schema.Constructor.eo__40_40aci_5fsorted args [] hinv h64 (.inl rfl)
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term___eo_List hx h.2
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term___eo_List_nil hx h.2
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term___eo_List_cons hx h.2
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term_Bool hx h.2
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term_Type hx h.2
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
  · obtain ⟨rfl, rfl⟩ := Embed.inv_Term_FunType hx h.2
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_Var hx h.2
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_DatatypeType hx h.2
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_Term_DatatypeTypeRef hx h.2
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_DtcAppType hx h.2
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
  · obtain ⟨x0, x1, x2, rfl, rfl⟩ := Embed.inv_Term_DtCons hx h.2
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
  · obtain ⟨x0, x1, x2, x3, rfl, rfl⟩ := Embed.inv_Term_DtSel hx h.2
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
  · obtain ⟨x0, rfl, rfl⟩ := Embed.inv_Term_USort hx h.2
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
  · obtain ⟨x0, x1, rfl, rfl⟩ := Embed.inv_Term_UConst hx h.2
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
