module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Literals

/-!
# Numerals and rationals: their literals in patterns and built from values

A pattern on a numeral or a rational literal (`$emb_Numeral`,
`$emb_Rational` with a field) is a `destruct` with the literal's
constructor: the runtime finds the literal and stores a native copy of its
value (`Hit::Raw` of `literal.clone()`), so the store changes, as for a
Boolean literal (`Runtime/Literals.lean`). Building such a literal from a
native value (`construct` with the constructor and one argument) reads
the value (`construct_literal`: a clone) and stores the literal.

The copies rest on `Trusted.lean`'s `Integer.clone_spec` and
`Rational.clone_spec`: that malachite's `clone` gives the same number.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-! ## Storing a numeral or a rational -/

/-- `raw` of a native numeral gives a handle of the integer. -/
theorem Store.raw_int_spec (s : Store) (i : Int) (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Numeral (num.Integer.ofInt i)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t i
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Numeral _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨Holds.native t.val _ hres.1 hres.2, trivial⟩

/-- `raw` of a native rational gives a handle of the rational. -/
theorem Store.raw_rat_spec (s : Store) (q : ℚ) (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Rational (num.Rational.ofRat q)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t q
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Rational _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨Holds.native t.val _ hres.1 hres.2, trivial⟩

/-- `literal` with a numeral gives a handle of the numeral term. -/
theorem Store.literal_numeral_spec (s : Store) (i : Int) (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Numeral (num.Integer.ofInt i)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Numeral i)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.literal
  simp only [Std.bind_ok]
  apply WP.dspec_mono (Store.intern_inv s (TermData.Literal (lit.Lit.Numeral _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, by simp [Embed.embedded_emb_Term, Embed.emb_Term]⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    exact Holds.lit t.val _ hres.1 hres.2

/-- `literal` with a rational gives a handle of the rational term. -/
theorem Store.literal_rational_spec (s : Store) (q : ℚ) (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Rational (num.Rational.ofRat q)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Rational q)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.literal
  simp only [Std.bind_ok]
  apply WP.dspec_mono (Store.intern_inv s (TermData.Literal (lit.Lit.Rational _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, by simp [Embed.embedded_emb_Term, Embed.emb_Term]⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    exact Holds.lit t.val _ hres.1 hres.2

/-! ## Patterns -/

/-- The literal destruct of the numeral constructor: a copy of a numeral
literal, nothing for any other. -/
theorem Store.destruct_literal_numeral (l : lit.Lit) :
    Store.destruct_literal Embedding.Numeral l =
      ok (match l with
        | lit.Lit.Numeral i => Hit.Raw (lit.Lit.Numeral i)
        | _ => Hit.Done none) := by
  cases l <;> simp [Store.destruct_literal, Embedding.Insts.CoreCmpPartialEqEmbedding.eq,
    Embedding.read_discriminant, lit.Lit.Insts.CoreCloneClone.clone, num.Integer.clone_spec]

/-- The literal destruct of the rational constructor: a copy of a rational
literal, nothing for any other. -/
theorem Store.destruct_literal_rational (l : lit.Lit) :
    Store.destruct_literal Embedding.Rational l =
      ok (match l with
        | lit.Lit.Rational q => Hit.Raw (lit.Lit.Rational q)
        | _ => Hit.Done none) := by
  cases l <;> simp [Store.destruct_literal, Embedding.Insts.CoreCmpPartialEqEmbedding.eq,
    Embedding.read_discriminant, lit.Lit.Insts.CoreCloneClone.clone, num.Rational.clone_spec]

/-- No term is stored as a node of the numeral literal's constructor. -/
theorem enc_ne_node_numeral (x : Eo.Term) (xs : List Tree) :
    Embedded.enc x ≠ Tree.node schema.Constructor.eo__24emb_5fNumeral xs := by
  intro h
  cases x
  all_goals first | (simp [Embed.embedded_enc_Term, Embed.enc_Term] at h; done) | skip
  rename_i y
  cases y <;> simp [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] at h

/-- No term is stored as a node of the rational literal's constructor. -/
theorem enc_ne_node_rational (x : Eo.Term) (xs : List Tree) :
    Embedded.enc x ≠ Tree.node schema.Constructor.eo__24emb_5fRational xs := by
  intro h
  cases x
  all_goals first | (simp [Embed.embedded_enc_Term, Embed.enc_Term] at h; done) | skip
  rename_i y
  cases y <;> simp [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] at h

/-- `destruct` with `$emb_Numeral` on a handle of a term: a handle of the
native integer of a numeral literal, and nothing for any other term. -/
theorem Store.destruct_numeral_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fNumeral t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (f : Term) (i : Int), x = Eo.Term.Numeral i ∧ v.val = [f] ∧ Represents.rep s' f i
      | core.result.Result.Ok none => ∀ i, x ≠ Eo.Term.Numeral i
      | core.result.Result.Err _ => True ⦄div := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.destruct
  simp only [show schema.Constructor.embedding schema.Constructor.eo__24emb_5fNumeral =
    ok Embedding.Numeral from rfl, Std.bind_ok]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have none_ok : (∀ i, tx ≠ Tree.lit (lit.Lit.Numeral (num.Integer.ofInt i))) →
      ∀ i, x ≠ Eo.Term.Numeral i := by
    intro hn i hi; subst hi
    exact hn i (by rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term])
  cases hh with
  | lit _ l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · simp only [Store.destruct_literal_numeral, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun i h => by cases h⟩
    · simp only [Store.destruct_literal_numeral, Std.bind_ok]
      step with Store.raw_int_spec s i hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv1, hg1⟩
      | Ok f =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
          WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, f, i, rfl, rfl, hr⟩
    all_goals
      simp only [Store.destruct_literal_numeral, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun i h => by cases h⟩
  | node _ d v xs _ hd _ =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec schema.Constructor.eo__24emb_5fNumeral
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    simp only [h1, h2, Std.bind_ok]
    have hnd : n1 ≠ n2 := by
      intro he; subst he
      have hdc := schema.Constructor.code_inj h2 h1
      subst hdc
      exact enc_ne_node_numeral x xs hx
    simp only [hnd, ite_false, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun i h => by cases h)⟩
  | _ =>
    rename_i hd
    first
      | (simp only [hd, WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun i h => by cases h)⟩)
      | (rename_i _ hd'
         simp only [hd', WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun i h => by cases h)⟩)

/-- `destruct` with `$emb_Rational` on a handle of a term: a handle of the
native rational of a rational literal, and nothing for any other term. -/
theorem Store.destruct_rational_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fRational t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (f : Term) (q : ℚ), x = Eo.Term.Rational q ∧ v.val = [f] ∧ Represents.rep s' f q
      | core.result.Result.Ok none => ∀ q, x ≠ Eo.Term.Rational q
      | core.result.Result.Err _ => True ⦄div := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.destruct
  simp only [show schema.Constructor.embedding schema.Constructor.eo__24emb_5fRational =
    ok Embedding.Rational from rfl, Std.bind_ok]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have none_ok : (∀ q, tx ≠ Tree.lit (lit.Lit.Rational (num.Rational.ofRat q))) →
      ∀ q, x ≠ Eo.Term.Rational q := by
    intro hn q hq; subst hq
    exact hn q (by rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term])
  cases hh with
  | lit _ l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · simp only [Store.destruct_literal_rational, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun q h => by cases h⟩
    · simp only [Store.destruct_literal_rational, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun q h => by cases h⟩
    · simp only [Store.destruct_literal_rational, Std.bind_ok]
      step with Store.raw_rat_spec s q hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv1, hg1⟩
      | Ok f =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
          WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, f, q, rfl, rfl, hr⟩
    all_goals
      simp only [Store.destruct_literal_rational, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun q h => by cases h⟩
  | node _ d v xs _ hd _ =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec schema.Constructor.eo__24emb_5fRational
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    simp only [h1, h2, Std.bind_ok]
    have hnd : n1 ≠ n2 := by
      intro he; subst he
      have hdc := schema.Constructor.code_inj h2 h1
      subst hdc
      exact enc_ne_node_rational x xs hx
    simp only [hnd, ite_false, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun q h => by cases h)⟩
  | _ =>
    rename_i hd
    first
      | (simp only [hd, WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun q h => by cases h)⟩)
      | (rename_i _ hd'
         simp only [hd', WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun q h => by cases h)⟩)

/-! ## Built from a native value -/

/-- What a handle of a native value stands for in the store. -/
theorem Store.rep_native_data {α : Type} [Embedded α] {s : Store} {t : Term} {x : α}
    {l : lit.Lit} (h : Represents.rep s t x) (he : Embedded.enc x = Tree.native l) :
    t.val < s.nodes.length ∧ s.nodes.val[t.val]! = TermData.Native l := by
  obtain ⟨hh, _⟩ := h
  rw [he] at hh
  cases hh with
  | native _ _ hlt hd => exact ⟨hlt, hd⟩

/-- `construct_literal` with an embedding of numerals, on a handle of a
native integer: the numeral term. -/
theorem Store.construct_literal_numeral_spec (s : Store) {a : Term} {i : Int}
    (h : Represents.rep s a i) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct_literal s Embedding.Numeral a ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Numeral i)
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hlt, hd⟩ := Store.rep_native_data (l := lit.Lit.Numeral (num.Integer.ofInt i)) h rfl
  unfold Store.construct_literal
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hd,
    Embedding.Insts.CoreCmpPartialEqEmbedding.eq, Embedding.read_discriminant, decide_true,
    ite_true, lit.Lit.Insts.CoreCloneClone.clone, num.Integer.clone_spec]
  exact Store.literal_numeral_spec s i hinv h64

/-- `construct_literal` with an embedding of rationals, on a handle of a
native rational: the rational term. -/
theorem Store.construct_literal_rational_spec (s : Store) {a : Term} {q : ℚ}
    (h : Represents.rep s a q) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct_literal s Embedding.Rational a ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Rational q)
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hlt, hd⟩ := Store.rep_native_data (l := lit.Lit.Rational (num.Rational.ofRat q)) h rfl
  unfold Store.construct_literal
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hd,
    Embedding.Insts.CoreCmpPartialEqEmbedding.eq, Embedding.read_discriminant, decide_true,
    ite_true, lit.Lit.Insts.CoreCloneClone.clone, num.Rational.clone_spec]
  exact Store.literal_rational_spec s q hinv h64

/-- `construct` of `eo__24emb_5fNumeral` with the handle of a native value: the
numeral term. -/
theorem Store.construct_numeral_spec (s : Store) (args : Slice Term) {a0 : Term} {x0 : Int}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fNumeral args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.Numeral x0)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.construct
  obtain ⟨n, hn⟩ := schema.Constructor.arity_ok schema.Constructor.eo__24emb_5fNumeral
  rw [hn]
  simp only [Std.bind_ok]
  by_cases harity : (n != args.len) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true harity)]
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, trivial⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false harity)]
    step with Store.check_handles_loop_spec as ⟨r, hr⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact ⟨hinv, Store.Grows.refl s⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      have hemb : schema.Constructor.embedding schema.Constructor.eo__24emb_5fNumeral =
          ok Embedding.Numeral := rfl
      rw [hemb]
      have hlen : Slice.len args = 1#usize := by
        simp [Slice.len, hargs]; scalar_tac
      have hidx : Slice.index_usize args 0#usize = ok a0 := by
        simp [Slice.index_usize, hargs]
      simp only [Std.bind_ok, hlen, ite_true, hidx]
      exact Store.construct_literal_numeral_spec s h0 hinv h64

/-- `construct` of `eo__24emb_5fRational` with the handle of a native value: the
rational term. -/
theorem Store.construct_rational_spec (s : Store) (args : Slice Term) {a0 : Term} {x0 : ℚ}
    (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fRational args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.Rational x0)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.construct
  obtain ⟨n, hn⟩ := schema.Constructor.arity_ok schema.Constructor.eo__24emb_5fRational
  rw [hn]
  simp only [Std.bind_ok]
  by_cases harity : (n != args.len) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true harity)]
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, trivial⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false harity)]
    step with Store.check_handles_loop_spec as ⟨r, hr⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact ⟨hinv, Store.Grows.refl s⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      have hemb : schema.Constructor.embedding schema.Constructor.eo__24emb_5fRational =
          ok Embedding.Rational := rfl
      rw [hemb]
      have hlen : Slice.len args = 1#usize := by
        simp [Slice.len, hargs]; scalar_tac
      have hidx : Slice.index_usize args 0#usize = ok a0 := by
        simp [Slice.index_usize, hargs]
      simp only [Std.bind_ok, hlen, ite_true, hidx]
      exact Store.construct_literal_rational_spec s h0 hinv h64

end pathos_compiled_checker
