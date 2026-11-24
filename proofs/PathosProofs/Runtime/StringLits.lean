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
public import PathosProofs.Runtime.IntNatives

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
    Embedded.enc x ≠ Tree.node schema.Constructor.eo__24emb_5fString xs :=
  enc_ne_node_of (e := Embedding.Str) rfl nofun nofun xs

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

/-! ## String constants -/

/-- A vector of `u32` is the runtime's form of the code points it holds:
they are below `2^32`, and their number fits a vector. -/
theorem Tree.strOf_of_vec (v : alloc.vec.Vec Std.U32) :
    Tree.strOf (v.val.map (fun c => c.val)) = v ∧ Tree.okStr (v.val.map (fun c => c.val)) := by
  have hl : (v.val.map (fun c => c.val)).length ≤ Usize.max := by
    simpa using v.property
  refine ⟨?_, hl, ?_⟩
  · unfold Tree.strOf
    rw [dif_pos hl]
    apply alloc.vec.Vec.ext
    rw [alloc.vec.Vec.from_val, List.map_map]
    conv => rhs; rw [← List.map_id v.val]
    apply List.map_congr_left
    intro c _
    show Tree.u32Wrap c.val = c
    unfold Tree.u32Wrap
    cases c with
    | mk bv => simp
  · intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨u, _, rfl⟩ := hc
    exact u.hBounds

/-- `raw` of a string literal built from code points (a string constant of
the generated code, `EoString::from_code_points(vec![…])`) gives a handle
of the string they spell. -/
theorem Store.raw_str_vec_spec (s : Store) (v : alloc.vec.Vec Std.U32) (str : List Nat)
    (h : v.val.map (fun c => c.val) = str) (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Str v) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t str
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hv, hok⟩ := Tree.strOf_of_vec v
  subst h
  conv => arg 1; rw [← hv]
  exact Store.raw_str_spec s _ hok hinv h64

/-- `literal` with a string constant as the generated code builds it, from
a vector of code points: a handle of the string term. -/
theorem Store.literal_str_vec_spec (s : Store) (v : alloc.vec.Vec Std.U32) (str : List Nat)
    (h : v.val.map (fun c => c.val) = str) (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Str v) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.String str)
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hv, hok⟩ := Tree.strOf_of_vec v
  subst h
  conv => arg 1; rw [← hv]
  exact Store.literal_string_spec s _ hok hinv h64

/-- A fact about a handle carries over to an equal value (for a string
constant: from its code points to logos's literal, once both are
concrete). -/
theorem Represents.rep_of_eq {α : Type} [Embedded α] {s : Store} {t : Term} {x y : α}
    (h : Represents.rep s t x) (e : x = y) : Represents.rep s t y := e ▸ h

/-! ## Binary literals in patterns -/

/-- The literal destruct of the binary constructor: the width and the value
of a binary literal as two numerals, nothing for any other. -/
theorem Store.destruct_literal_binary (l : lit.Lit) :
    Store.destruct_literal Embedding.Binary l =
      ok (match l with
        | lit.Lit.Binary b => Hit.Binary (num.Integer.ofInt b.size.val) b.value
        | _ => Hit.Done none) := by
  cases l <;> simp [Store.destruct_literal, Embedding.Insts.CoreCmpPartialEqEmbedding.eq,
    Embedding.read_discriminant, bitvec.BitVec.impl.size, bitvec.BitVec.impl.value,
    num.Integer.from_u32_spec, num.Integer.clone_spec]

/-- No term is stored as a node of the binary literal's constructor. -/
theorem enc_ne_node_binary (x : Eo.Term) (xs : List Tree) :
    Embedded.enc x ≠ Tree.node schema.Constructor.eo__24emb_5fBinary xs :=
  enc_ne_node_of (e := Embedding.Binary) rfl nofun nofun xs

/-- `destruct` with `$emb_Binary` on a handle of a term: handles of the
width and the value of a binary literal, and nothing for any other term. -/
theorem Store.destruct_binary_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fBinary t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (f g : Term) (w n : Int), x = Eo.Term.Binary w n ∧ v.val = [f, g] ∧
          Represents.rep s' f w ∧ Represents.rep s' g n
      | core.result.Result.Ok none => ∀ w n, x ≠ Eo.Term.Binary w n
      | core.result.Result.Err _ => True ⦄div := by
  have hlt := h.lt
  obtain ⟨hh, he⟩ := h
  unfold Store.destruct
  simp only [show schema.Constructor.embedding schema.Constructor.eo__24emb_5fBinary =
    ok Embedding.Binary from rfl, Std.bind_ok]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have none_ok : (∀ w n, tx ≠ Tree.lit (lit.Lit.Binary (Tree.bvOf w n))) →
      ∀ w n, x ≠ Eo.Term.Binary w n := by
    intro hn w n hi; subst hi
    exact hn w n (by rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term])
  cases hh with
  | lit _ l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
    · simp only [Store.destruct_literal_binary, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun _ _ h => by cases h⟩
    · simp only [Store.destruct_literal_binary, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun _ _ h => by cases h⟩
    · simp only [Store.destruct_literal_binary, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun _ _ h => by cases h⟩
    · simp only [Store.destruct_literal_binary, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun _ _ h => by cases h⟩
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
      have hw : ((Tree.bvOf w n).size.val : Int) = w := Tree.bvW_bvOf w n he
      simp only [Store.destruct_literal_binary, Std.bind_ok, hw]
      step with Store.raw_int_spec s w hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv1, hg1⟩
      | Ok f =>
        have hv : (Tree.bvOf w n).value = num.Integer.ofInt n := rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, hv]
        step with Store.raw_int_spec s1 n hinv1 h64 as ⟨r2, s2, hinv2, hg2, hr2⟩
        cases r2 with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          exact ⟨hinv2, hg1.trans hg2⟩
        | Ok g =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
            WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv2, hg1.trans hg2, f, g, w, n, rfl, ?_, Represents.grows hr hg2, hr2⟩
          simp [alloc.slice.Slice.into_vec, Std.Array.to_slice, Array.make]
          rfl
  | node _ d v xs _ hd _ =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec schema.Constructor.eo__24emb_5fBinary
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    simp only [h1, h2, Std.bind_ok]
    have hnd : n1 ≠ n2 := by
      intro he; subst he
      have hdc := schema.Constructor.code_inj h2 h1
      subst hdc
      exact enc_ne_node_binary x xs hx
    simp only [hnd, ite_false, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ h => by cases h)⟩
  | _ =>
    rename_i hd
    first
      | (simp only [hd, WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ h => by cases h)⟩)
      | (rename_i _ hd'
         simp only [hd', WP.dspec_ok, WP.uncurry'_pair, Std.bind_ok]
         exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ h => by cases h)⟩)

/-! ## Building a binary literal from its width and value -/

/-- What a handle of a binary term says of its width and value: they are
in range. -/
theorem Store.rep_binary_okBv {s : Store} {t : Term} {w n : Int}
    (h : Represents.rep s t (Eo.Term.Binary w n)) : Tree.okBv w n := by
  have := h.2
  simpa [Embed.embedded_emb_Term, Embed.emb_Term] using this

/-- `literal` with a binary constant as the generated code builds it,
`BitVec::new(<w>, &Integer::from(<n>u32))`: after the specs of `from` and
`mod_by_pow2`, a handle of the binary term, for a value in range. -/
theorem Store.literal_binary_u32_spec (s : Store) (w n : Std.U32) (wi ni : Int)
    (hw : (w.val : Int) = wi) (hn : (n.val : Int) = ni) (hok : Tree.okBv wi ni)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Binary ({ size := w, value := num.Integer.ofInt (Int.emod (n.val : Int) (2 ^ w.val)) } : bitvec.BitVec)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Binary wi ni)
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hw0, hw1, hn0, hn1⟩ := hok
  have hmod : Int.emod (n.val : Int) (2 ^ w.val) = ni := by
    rw [hn]
    have : (2 : Int) ^ w.val = 2 ^ wi.toNat := by
      have : w.val = wi.toNat := by omega
      rw [this]
    rw [this]; exact Int.emod_eq_of_lt hn0 hn1
  have hw' : w = Tree.u32Wrap wi.toNat := by
    apply UScalar.eq_of_val_eq
    rw [Tree.u32Wrap_val _ (by omega)]
    omega
  have hbv : ({ size := w, value := num.Integer.ofInt (Int.emod (n.val : Int) (2 ^ w.val)) } :
      bitvec.BitVec) = Tree.bvOf wi ni := by
    rw [hmod, hw']; rfl
  rw [hbv]
  exact Store.literal_binary_spec s wi ni ⟨hw0, hw1, hn0, hn1⟩ hinv h64

/-- `construct_binary` on handles of a width and a value in range: the
binary term. -/
theorem Store.construct_binary_spec' (s : Store) {a0 a1 : Term} {w n : Int}
    (h0 : Represents.rep s a0 w) (h1 : Represents.rep s a1 n) (hok : Tree.okBv w n)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.construct_binary s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Binary w n)
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hw0, hw1, hn0, hn1⟩ := hok
  unfold Store.construct_binary
  rw [Store.raw_int_rep h0, Store.raw_int_rep h1]
  simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, num.Integer.fits_u32_spec,
    num.Integer.toInt_ofInt]
  have hfit : (0 ≤ w ∧ w < 2 ^ 32) := ⟨hw0, hw1⟩
  simp only [hfit, and_self, decide_true, ite_true]
  obtain ⟨r, hr, hrv⟩ := num.Integer.to_u32_spec (num.Integer.ofInt w)
  rw [hr]
  simp only [num.Integer.toInt_ofInt, hfit, and_self, ite_true] at hrv
  simp only [Std.bind_ok, bitvec.BitVec.new, num.Integer.mod_by_pow2_spec, num.Integer.toInt_ofInt]
  have hpow : ((2 : Int) ^ r.val) = 2 ^ w.toNat := by
    have : r.val = w.toNat := by omega
    rw [this]
  have hmod : n % 2 ^ r.val = n := by
    rw [hpow]; exact Int.emod_eq_of_lt hn0 hn1
  have hr' : r = Tree.u32Wrap w.toNat := by
    apply UScalar.eq_of_val_eq
    rw [Tree.u32Wrap_val _ (by omega)]
    omega
  have hbv : ({ size := r, value := num.Integer.ofInt (Int.emod n (2 ^ r.val)) } :
      bitvec.BitVec) = Tree.bvOf w n := by
    rw [show Int.emod n (2 ^ r.val) = n from hmod, hr']; rfl
  rw [hbv]
  exact Store.literal_binary_spec s w n ⟨hw0, hw1, hn0, hn1⟩ hinv h64

/-- `construct` of `eo__24emb_5fBinary` with handles of a width and a value
in range: the binary term. -/
theorem Store.construct_binary_spec (s : Store) (args : Slice Term) {a0 a1 : Term}
    {w n : Int} (hargs : args.val = [a0, a1]) (h0 : Represents.rep s a0 w)
    (h1 : Represents.rep s a1 n) (hok : Tree.okBv w n) (hinv : s.Inv) (h64 : Platform64) :
    Store.construct s schema.Constructor.eo__24emb_5fBinary args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.Term.Binary w n)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.construct
  obtain ⟨k, hk⟩ := schema.Constructor.arity_ok schema.Constructor.eo__24emb_5fBinary
  rw [hk]
  simp only [Std.bind_ok]
  by_cases harity : (k != args.len) = true
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
      have hemb : schema.Constructor.embedding schema.Constructor.eo__24emb_5fBinary =
          ok Embedding.Binary := rfl
      rw [hemb]
      have hlen : Slice.len args = 2#usize := by
        simp [Slice.len, hargs]; scalar_tac
      have hidx0 : Slice.index_usize args 0#usize = ok a0 := by
        simp [Slice.index_usize, hargs]
      have hidx1 : Slice.index_usize args 1#usize = ok a1 := by
        simp [Slice.index_usize, hargs]
      simp only [Std.bind_ok, hlen, ite_true, hidx0, hidx1]
      exact Store.construct_binary_spec' s h0 h1 hok hinv h64

end pathos_compiled_checker
