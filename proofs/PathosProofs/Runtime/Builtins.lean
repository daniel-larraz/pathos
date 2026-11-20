module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Natives
public import PathosProofs.Runtime.Numbers

/-!
# Builtin operators on literals

`builtin_core` hands an operator on literals (`eo::len`, `eo::and`, …) to
`builtin_strict`, which gives the stuck term if an argument is stuck, and
then to `builtin_literal`: `literals` reads each argument's literal (a
clone, `literal_of`), `Lit::evaluate` computes the result or nothing, and
the result is stored as a literal, nothing as the stuck term.

Here the pieces every such operator needs, and `eo::len`: the width of a
binary, the number of characters of a string (`Integer::from` of a `u32`
or a `usize`).

These rest on `Trusted.lean`'s specs of `clone` (of an `Integer` and of a
`Rational`, inside a literal's clone) and of `from` (`from_u32_spec`,
`from_usize_spec`): what malachite computes, through `num.rs`.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-! ## Reading the literals -/

/-- A string's clone is the string. -/
theorem eostring_clone_eq (v : eostring.EoString) :
    eostring.EoString.Insts.CoreCloneClone.clone v = ok v := by
  unfold eostring.EoString.Insts.CoreCloneClone.clone alloc.vec.CloneVec.clone
  have h : ∀ x ∈ v.slice.val, core.clone.CloneU32.clone x = ok x := fun _ _ => rfl
  obtain ⟨s', hs, heq⟩ := spec_returns (Slice.clone_spec h)
  rw [hs]
  simp [← heq]

/-- A bit-vector's clone is the bit-vector. -/
theorem bitvec_clone_eq (b : bitvec.BitVec) :
    bitvec.BitVec.Insts.CoreCloneClone.clone b = ok b := by
  simp [bitvec.BitVec.Insts.CoreCloneClone.clone, num.Integer.clone_spec, lift,
    core.clone.impls.CloneU32.clone]

/-- A literal's clone is the literal. -/
theorem lit_clone_eq (l : lit.Lit) : lit.Lit.Insts.CoreCloneClone.clone l = ok l := by
  cases l <;> simp [lit.Lit.Insts.CoreCloneClone.clone, num.Integer.clone_spec,
    num.Rational.clone_spec, bitvec_clone_eq, eostring_clone_eq, lift,
    core.clone.impls.CloneBool.clone]

/-- `literal_of` on a handle: its literal, if it is one. -/
theorem Store.literal_of_eq (s : Store) (t : Term) (hlt : t.val < s.nodes.length) :
    Store.literal_of s t = ok (match s.nodes.val[t.val]! with
      | TermData.Literal l => some l
      | _ => none) := by
  unfold Store.literal_of
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok]
  cases s.nodes.val[t.val]! <;> simp [lit_clone_eq]

/-- `literals` on one handle: its literal, if it is one. -/
theorem Store.literals_one (s : Store) (args : Slice Term) {a : Term} (hargs : args.val = [a])
    (hlt : a.val < s.nodes.length) :
    Store.literals s args ⦃ o =>
      match o with
      | some v => ∃ l, v.val = [l] ∧ s.nodes.val[a.val]! = TermData.Literal l
      | none => ∀ l, s.nodes.val[a.val]! ≠ TermData.Literal l ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  unfold Store.literals
  unfold Store.literals_loop
  simp only [hlen]
  split
  case isFalse h => exact absurd (by scalar_tac) h
  step as ⟨t, ht⟩
  have hta : a = t := by simp [ht, hargs]
  subst hta
  rw [Store.literal_of_eq s a hlt]
  have hexit : ∀ (lits : alloc.vec.Vec lit.Lit) (all : Bool) (i : Std.Usize), i.val = 1 →
      Store.literals_loop s args lits all i = ok (lits, all) := by
    intro lits all i hi
    unfold Store.literals_loop
    have : ¬ (i < Slice.len args) := by
      have : (Slice.len args).val = 1 := by simp [Slice.len, hargs]
      scalar_tac
    simp [this]
  split
  · rename_i l hl
    simp only [Std.bind_ok]
    step with alloc.vec.Vec.push_spec (alloc.vec.Vec.with_capacity lit.Lit 1#usize) l
      (by simp [alloc.vec.Vec.with_capacity]; scalar_tac) as ⟨v1, hv1⟩
    step as ⟨i2, hi2⟩
    rw [hexit _ _ i2 (by scalar_tac)]
    simp
    exact ⟨l, by simp [hv1, alloc.vec.Vec.with_capacity], by simpa [hlt] using hl⟩
  · rename_i hnl
    simp only [Std.bind_ok]
    step as ⟨i2, hi2⟩
    rw [hexit _ _ i2 (by scalar_tac)]
    simpa [hlt] using hnl

/-! ## `eo::len` -/

/-- A literal's kind is not other than itself. -/
theorem litkind_ne_self (k : kind.LitKind) :
    core.cmp.PartialEq.ne.default kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq k k = ok false := by
  have h := core.cmp.PartialEq.ne.default.spec kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq k k
    (by cases k <;> simp [kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant])
  obtain ⟨b, hb, hiff⟩ := spec_returns h
  rw [hb]
  cases b <;> simp_all

theorem litkind_ne_self' (k : kind.LitKind) :
    core.cmp.PartialEq.ne.trait_default kind.LitKind.Insts.CoreCmpPartialEqLitKind k k =
      ok false := by
  unfold core.cmp.PartialEq.ne.trait_default
  exact litkind_ne_self k

/-- `all_of_kind`'s loop past the last literal. -/
theorem all_of_kind_loop_exit (args : Slice lit.Lit) (ka : kind.LitKind) (b : Bool)
    (i : Std.Usize) (h : args.length ≤ i.val) :
    lit.Lit.all_of_kind_loop args ka b i = ok b := by
  unfold lit.Lit.all_of_kind_loop
  have : ¬ (i < Slice.len args) := by
    have : (Slice.len args).val = args.length := by simp [Slice.len, Slice.length]
    scalar_tac
  simp [this]

/-- `Lit::evaluate` of `eo::len` on one literal: the width of a binary, the
length of a string, nothing for another literal. -/
theorem lit_evaluate_length (args : Slice lit.Lit) {l : lit.Lit} (hargs : args.val = [l]) :
    lit.Lit.evaluate kind.EvalOp.Length args ⦃ o => o = (match l with
      | lit.Lit.Binary b => some (lit.Lit.Numeral (num.Integer.ofInt (b.size.val : Int)))
      | lit.Lit.Str e => some (lit.Lit.Numeral (num.Integer.ofInt (e.val.length : Int)))
      | _ => none) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l := by simp [Slice.index_usize, hargs]
  have hl1 : Slice.length args = 1 := by simp [Slice.length, hargs]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l <;>
  · simp [hl1, h0, hlen, lit.Lit.kind, litkind_ne_self']
    step as ⟨i1, hi1⟩
    rw [all_of_kind_loop_exit args _ _ i1 (by scalar_tac)]
    simp [bitvec.BitVec.impl.size, eostring.EoString.len, alloc.vec.Vec.len,
      num.Integer.from_u32_spec, num.Integer.from_usize_spec]

/-- `any_stuck` on one handle of a term: whether the term is stuck. -/
theorem Store.any_stuck_one {s : Store} {args : Slice Term} {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) :
    Store.any_stuck s args ⦃ r => r = decide (x = Eo.Term.Stuck) ⦄ := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  unfold Store.any_stuck
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt0 : (0#usize : Std.Usize) < 1#usize := by scalar_tac
  simp only [hlt0, ite_true]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  simp only [h0, Store.stuck_or_foreign_rep ha, Std.bind_ok]
  cases hx : decide (x = Eo.Term.Stuck) <;>
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    step as ⟨i1, hi1⟩
    unfold Store.any_stuck_loop
    simp only [hlen]
    have : ¬ (i1 < 1#usize) := by scalar_tac
    simp [this]

/-- A stored string's length is its number of characters. -/
theorem strOf_length (x : List Nat) (h : Tree.okStr x) : (Tree.strOf x).val.length = x.length := by
  obtain ⟨hl, _⟩ := h
  simp [Tree.strOf, hl]

/-- `eo::len`: the width of a binary, the number of characters of a
string, the stuck term for any other term. -/
theorem Store.builtin_spec_len (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.Length args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_len x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.Length 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0]
    unfold Store.builtin_strict
    step with Store.any_stuck_one hargs ha as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_len Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__eo_len]
      rw [this]; exact hinv.rep_stuck
    simp only [hx, decide_false, Bool.false_eq_true, ite_false, kind.EvalOp.is_list_op,
      Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_one s args hargs ha.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_len x = Eo.Term.Stuck := by
        obtain ⟨hh, he⟩ := ha
        unfold Eo.__eo_len
        split
        · rename_i s0
          exfalso
          simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
          cases hh with | lit _ _ _ hd => exact ho _ hd
        · rename_i w n
          exfalso
          simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
          cases hh with | lit _ _ _ hd => exact ho _ hd
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l, hv, hd⟩ := ho
      simp only
      step with lit_evaluate_length (alloc.vec.Vec.deref v) (l := l) (by simp [alloc.vec.Vec.deref, hv]) as ⟨o1, ho1⟩
      subst ho1
      obtain ⟨hh, he⟩ := ha
      generalize hxe : Embedded.enc x = tx at hh
      cases hh with
      | lit _ l' _ hd' =>
        have hl : l' = l := by
          have h := hd'.symm.trans hd
          injection h
        subst hl
        rcases Embed.inv_Term_lit (by simpa [Embed.embedded_enc_Term] using hxe) with
          ⟨b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨str, rfl, rfl⟩ | ⟨w, n, rfl, rfl⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_len] using hinv.rep_stuck⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_len] using hinv.rep_stuck⟩
        · simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_len] using hinv.rep_stuck⟩
        · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
          have hlen' : ((Tree.strOf str).val.length : Int) = Eo.native_str_len str := by
            rw [strOf_length str he]; rfl
          simp only [hlen']
          have hv : Eo.__eo_len (Eo.Term.String str) = Eo.Term.Numeral (Eo.native_str_len str) := by
            simp [Eo.__eo_len]
          rw [hv]
          exact Store.literal_numeral_spec s (Eo.native_str_len str) hinv h64
        · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
          have hw : ((Tree.bvOf w n).size.val : Int) = w := Tree.bvW_bvOf w n he
          simp only [hw]
          have hv : Eo.__eo_len (Eo.Term.Binary w n) = Eo.Term.Numeral w := by
            simp [Eo.__eo_len]
          rw [hv]
          exact Store.literal_numeral_spec s w hinv h64
      | stuck _ _ hd' => cases hd'.symm.trans hd
      | native _ _ _ hd' => cases hd'.symm.trans hd
      | userop _ _ _ hd' => cases hd'.symm.trans hd
      | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
      | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

end pathos_compiled_checker
