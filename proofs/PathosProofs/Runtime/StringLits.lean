module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Numbers
public import PathosProofs.Runtime.Builtins

/-!
# String literals in patterns and as native values

A pattern on a string literal (`$emb_String` with a field) is a
`destruct` with the literal's constructor: the runtime finds the literal
and stores a native copy of its code points (`Hit::Raw` of
`literal.clone()`), as for numerals (`Runtime/Numbers.lean`). `EoString`'s
`clone` is translated code (a clone of the vector of `u32`), so no trusted
spec is needed. A string the store holds is in range (`okStr`: code points
below `2^32`, a length that fits a vector), and the embedding of terms
says so for every string literal.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `raw` of a native string in range gives a handle of the string. -/
theorem Store.raw_str_spec (s : Store) (str : List Nat) (hok : Tree.okStr str) (hinv : s.Inv)
    (h64 : Platform64) :
    Store.raw s (lit.Lit.Str (Tree.strOf str)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t str
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Str _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨Holds.native t.val _ hres.1 hres.2, hok⟩

/-- The literal destruct of the string constructor: a copy of a string
literal, nothing for any other. -/
theorem Store.destruct_literal_string (l : lit.Lit) :
    Store.destruct_literal Embedding.Str l =
      ok (match l with
        | lit.Lit.Str v => Hit.Raw (lit.Lit.Str v)
        | _ => Hit.Done none) := by
  cases l <;> simp [Store.destruct_literal, Embedding.Insts.CoreCmpPartialEqEmbedding.eq,
    Embedding.read_discriminant, lit.Lit.Insts.CoreCloneClone.clone, eostring_clone_eq]

/-- No term is stored as a node of the string literal's constructor. -/
theorem enc_ne_node_string (x : Eo.Term) (xs : List Tree) :
    Embedded.enc x ≠ Tree.node schema.Constructor.eo__24emb_5fString xs := by
  intro h
  cases x
  all_goals first | (simp [Embed.embedded_enc_Term, Embed.enc_Term] at h; done) | skip
  rename_i y
  cases y <;> simp [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop] at h

/-- `destruct` with `$emb_String` on a handle of a term: a handle of the
native string of a string literal, and nothing for any other term. -/
theorem Store.destruct_string_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fString t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (f : Term) (str : List Nat), x = Eo.Term.String str ∧ v.val = [f] ∧
          Represents.rep s' f str
      | core.result.Result.Ok none => ∀ str, x ≠ Eo.Term.String str
      | core.result.Result.Err _ => True ⦄div := by
  have hlt := h.lt
  obtain ⟨hh, he⟩ := h
  unfold Store.destruct
  simp only [show schema.Constructor.embedding schema.Constructor.eo__24emb_5fString =
    ok Embedding.Str from rfl, Std.bind_ok]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have none_ok : (∀ str, tx ≠ Tree.lit (lit.Lit.Str (Tree.strOf str))) →
      ∀ str, x ≠ Eo.Term.String str := by
    intro hn str hi; subst hi
    exact hn str (by rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term])
  cases hh with
  | lit _ l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨str, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · simp only [Store.destruct_literal_string, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun i h => by cases h⟩
    · simp only [Store.destruct_literal_string, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun i h => by cases h⟩
    · simp only [Store.destruct_literal_string, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun i h => by cases h⟩
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
      simp only [Store.destruct_literal_string, Std.bind_ok]
      step with Store.raw_str_spec s str he hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv1, hg1⟩
      | Ok f =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
          WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, f, str, rfl, rfl, hr⟩
    · simp only [Store.destruct_literal_string, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun i h => by cases h⟩
  | node _ d v xs _ hd _ =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec schema.Constructor.eo__24emb_5fString
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    simp only [h1, h2, Std.bind_ok]
    have hnd : n1 ≠ n2 := by
      intro he; subst he
      have hdc := schema.Constructor.code_inj h2 h1
      subst hdc
      exact enc_ne_node_string x xs hx
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

/-! ## Building a string literal from a native string -/

/-- `literal` with a string in range gives a handle of the string term. -/
theorem Store.literal_string_spec (s : Store) (str : List Nat) (hok : Tree.okStr str)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Str (Tree.strOf str)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.String str)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.literal
  simp only [Std.bind_ok]
  apply WP.dspec_mono (Store.intern_inv s (TermData.Literal (lit.Lit.Str _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, by simpa [Embed.embedded_emb_Term, Embed.emb_Term] using hok⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    exact Holds.lit t.val _ hres.1 hres.2

/-- `construct_literal` with an embedding of strings, on a handle of a
native string: the string term. -/
theorem Store.construct_literal_string_spec (s : Store) {a : Term} {str : List Nat}
    (h : Represents.rep s a str) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct_literal s Embedding.Str a ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.String str)
      | core.result.Result.Err _ => True ⦄div := by
  have hok : Tree.okStr str := h.2
  obtain ⟨hlt, hd⟩ := Store.rep_native_data (l := lit.Lit.Str (Tree.strOf str)) h rfl
  unfold Store.construct_literal
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hd,
    Embedding.Insts.CoreCmpPartialEqEmbedding.eq, Embedding.read_discriminant, decide_true,
    ite_true, lit.Lit.Insts.CoreCloneClone.clone, eostring_clone_eq]
  exact Store.literal_string_spec s str hok hinv h64

/-- `construct` of `eo__24emb_5fString` with the handle of a native string:
the string term. -/
theorem Store.construct_string_spec (s : Store) (args : Slice Term) {a0 : Term}
    {x0 : List Nat} (hargs : args.val = [a0]) (h0 : Represents.rep s a0 x0) (hinv : s.Inv)
    (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fString args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.String x0)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.construct
  obtain ⟨n, hn⟩ := schema.Constructor.arity_ok schema.Constructor.eo__24emb_5fString
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
      have hemb : schema.Constructor.embedding schema.Constructor.eo__24emb_5fString =
          ok Embedding.Str := rfl
      rw [hemb]
      have hlen : Slice.len args = 1#usize := by
        simp [Slice.len, hargs]; scalar_tac
      have hidx : Slice.index_usize args 0#usize = ok a0 := by
        simp [Slice.index_usize, hargs]
      simp only [Std.bind_ok, hlen, ite_true, hidx]
      exact Store.construct_literal_string_spec s h0 hinv h64

end pathos_compiled_checker
