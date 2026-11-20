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

/-- `literals` on two handles: their literals, if both are. -/
theorem Store.literals_two (s : Store) (args : Slice Term) {a b : Term}
    (hargs : args.val = [a, b]) (hla : a.val < s.nodes.length) (hlb : b.val < s.nodes.length) :
    Store.literals s args ⦃ o =>
      match o with
      | some v => ∃ l1 l2, v.val = [l1, l2] ∧ s.nodes.val[a.val]! = TermData.Literal l1 ∧
          s.nodes.val[b.val]! = TermData.Literal l2
      | none => ¬ ((∃ l1, s.nodes.val[a.val]! = TermData.Literal l1) ∧
          (∃ l2, s.nodes.val[b.val]! = TermData.Literal l2)) ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have hexit : ∀ (lits : alloc.vec.Vec lit.Lit) (all : Bool) (i : Std.Usize), i.val = 2 →
      Store.literals_loop s args lits all i = ok (lits, all) := by
    intro lits all i hi
    unfold Store.literals_loop
    have : ¬ (i < Slice.len args) := by
      have : (Slice.len args).val = 2 := by simp [Slice.len, hargs]
      scalar_tac
    simp [this]
  unfold Store.literals
  unfold Store.literals_loop
  simp only [hlen]
  split
  case isFalse h => exact absurd (by scalar_tac) h
  step as ⟨t, ht⟩
  have hta : a = t := by simp [ht, hargs]
  subst hta
  rw [Store.literal_of_eq s a hla]
  -- the second round
  have hsecond : ∀ (lits : alloc.vec.Vec lit.Lit) (all : Bool) (i1 : Std.Usize), i1.val = 1 →
      lits.val.length ≤ 1 →
      Store.literals_loop s args lits all i1 ⦃ r =>
        match s.nodes.val[b.val]! with
        | TermData.Literal l2 => ∃ v, r = (v, all) ∧ v.val = lits.val ++ [l2]
        | _ => r.2 = false ⦄ := by
    intro lits all i1 hi1 hl
    unfold Store.literals_loop
    simp only [hlen]
    split
    case isFalse h => exact absurd (by scalar_tac) h
    step as ⟨t, ht⟩
    have htb : b = t := by
      have : i1.val = 1 := by scalar_tac
      simp [ht, hargs, this]
    subst htb
    rw [Store.literal_of_eq s b hlb]
    split
    · rename_i l2 hl2
      simp only [Std.bind_ok]
      step with alloc.vec.Vec.push_spec lits l2 (by scalar_tac) as ⟨v1, hv1⟩
      step as ⟨i2, hi2⟩
      rw [hexit _ _ i2 (by scalar_tac)]
      simp [hl2, hv1]
    · rename_i hnl
      simp only [Std.bind_ok]
      step as ⟨i2, hi2⟩
      rw [hexit _ _ i2 (by scalar_tac)]
      simp only [WP.spec_ok]
  split
  · rename_i l1 hl1
    simp only [Std.bind_ok]
    step with alloc.vec.Vec.push_spec (alloc.vec.Vec.with_capacity lit.Lit 2#usize) l1
      (by simp [alloc.vec.Vec.with_capacity]; scalar_tac) as ⟨v1, hv1⟩
    step as ⟨i1, hi1⟩
    step with hsecond v1 true i1 (by scalar_tac) (by simp [hv1, alloc.vec.Vec.with_capacity])
      as ⟨lits1, all1, hr⟩
    split at hr
    · rename_i l2 hl2
      obtain ⟨hall, hv⟩ := hr
      subst hall
      simp only [ite_true, WP.spec_ok]
      exact ⟨l1, l2, by simp [hv, hv1, alloc.vec.Vec.with_capacity], hl1, hl2⟩
    · rename_i hnl2
      subst hr
      simp only [Bool.false_eq_true, ite_false, WP.spec_ok]
      rintro ⟨_, ⟨l2, hl2⟩⟩
      exact hnl2 l2 hl2
  · rename_i hnl1
    simp only [Std.bind_ok]
    step as ⟨i1, hi1⟩
    step with hsecond (alloc.vec.Vec.with_capacity lit.Lit 2#usize) false i1 (by scalar_tac)
      (by simp [alloc.vec.Vec.with_capacity]) as ⟨lits1, all1, hr⟩
    have hr2 : all1 = false := by
      split at hr
      · exact hr.1
      · simpa using hr
    subst hr2
    simp only [Bool.false_eq_true, ite_false, WP.spec_ok]
    rintro ⟨⟨l1, hl1⟩, _⟩
    exact hnl1 l1 hl1

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

/-! ## `eo::and` -/

/-- `!=` on two different literal kinds. -/
theorem litkind_ne {k1 k2 : kind.LitKind} (h : k1 ≠ k2) :
    core.cmp.PartialEq.ne.trait_default kind.LitKind.Insts.CoreCmpPartialEqLitKind k1 k2 =
      ok true := by
  unfold core.cmp.PartialEq.ne.trait_default
  have h' := core.cmp.PartialEq.ne.default.spec kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq k1 k2
    (by cases k1 <;> cases k2 <;> simp [kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant])
  obtain ⟨b, hb, hiff⟩ := spec_returns h'
  rw [hb]
  cases b
  · exfalso
    cases k1 <;> cases k2 <;> simp_all [kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant]
  · rfl

/-- A literal that stands for a term: neither hexadecimal nor decimal (the
embedding writes binaries and rationals). -/
def TermLit : lit.Lit → Prop
  | lit.Lit.Hex _ => False
  | lit.Lit.Decimal _ => False
  | _ => True

/-- What `Lit::evaluate` gives for `eo::and` on two literals that stand for
terms. -/
noncomputable def andLit : lit.Lit → lit.Lit → Option lit.Lit
  | lit.Lit.Boolean b1, lit.Lit.Boolean b2 => some (lit.Lit.Boolean (b1 && b2))
  | lit.Lit.Binary c1, lit.Lit.Binary c2 =>
    if c1.size = c2.size then
      some (lit.Lit.Binary ⟨c1.size, num.Integer.ofInt
        (Int.emod (Int.land c1.value.toInt c2.value.toInt) (2 ^ c1.size.val))⟩)
    else none
  | _, _ => none

theorem fold_bool_and (args : Slice lit.Lit) (b1 b2 : Bool) (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Boolean b2)) :
    lit.Lit.fold_bool kind.EvalOp.And b1 args ⦃ o => o = some (lit.Lit.Boolean (b1 && b2)) ⦄ := by
  unfold lit.Lit.fold_bool lit.Lit.fold_bool_loop
  cases b1 <;>
  · simp [hlen, h1 1#usize (by simp), lit.Lit.as_bool]
    step as ⟨j, hj⟩
    unfold lit.Lit.fold_bool_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp [hlen, hj2]

theorem fold_bv_and (args : Slice lit.Lit) (c1 c2 : bitvec.BitVec)
    (hlen : Slice.len args = 2#usize)
    (h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok (lit.Lit.Binary c2)) :
    lit.Lit.fold_bv kind.EvalOp.And kind.LitKind.Binary c1 args ⦃ o =>
      o = andLit (lit.Lit.Binary c1) (lit.Lit.Binary c2) ⦄ := by
  unfold lit.Lit.fold_bv lit.Lit.all_of_size lit.Lit.all_of_size_loop
  simp [hlen, h1 1#usize (by simp), lit.Lit.as_bv, lit.Lit.is_bv_of_size,
    bitvec.BitVec.impl.size]
  by_cases hs : c2.size = c1.size
  · simp only [hs, ite_true, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp only [hlen, hj2, ite_false, Std.bind_ok, ite_true]
    unfold lit.Lit.fold_bv_loop1
    simp [hlen, h1 1#usize (by simp), lit.Lit.as_bv, bitvec.BitVec.Insts.CoreCloneClone.clone,
      core.clone.impls.CloneU32.clone, num.Integer.clone_spec, bitvec.BitVec.and,
      bitvec.BitVec.new, num.Integer.bitwise_and_spec, num.Integer.mod_by_pow2_spec]
    step as ⟨k, hk⟩
    subst hk
    step as ⟨k2, hk2⟩
    have hk3 : ¬ (k2.val ≤ 1) := by scalar_tac
    simp [hk3, num.Integer.toInt_ofInt, lit.Lit.bitvec, kind.LitKind.Insts.CoreCmpPartialEqLitKind.eq,
      kind.LitKind.read_discriminant, andLit, hs]
    unfold lit.Lit.fold_bv_loop1
    have hk4 : ¬ k2 < 2#usize := by scalar_tac
    simp [hlen, hk4]
  · simp only [hs, ite_false, Std.bind_ok]
    step as ⟨j, hj⟩
    unfold lit.Lit.all_of_size_loop
    have hj2 : ¬ j < 2#usize := by scalar_tac
    simp [hlen, hj2, andLit, Ne.symm hs]

theorem lit_evaluate_and (args : Slice lit.Lit) {l1 l2 : lit.Lit} (hargs : args.val = [l1, l2])
    (ht1 : TermLit l1) (ht2 : TermLit l2) :
    lit.Lit.evaluate kind.EvalOp.And args ⦃ o => o = andLit l1 l2 ⦄ := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok l1 := by simp [Slice.index_usize, hargs]
  have hl2 : Slice.length args = 2 := by simp [Slice.length, hargs]
  have h1 : ∀ i : Std.Usize, i.val = 1 → Slice.index_usize args i = ok l2 := by
    intro i hi; simp [Slice.index_usize, hargs, hi]
  unfold lit.Lit.evaluate lit.Lit.all_of_kind lit.Lit.all_of_kind_loop
  cases l1 <;> cases l2 <;> simp only [TermLit] at ht1 ht2 <;>
  first
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne]
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp [andLit]
     done)
  | (simp [hl2, h0, hlen, lit.Lit.kind, litkind_ne_self']
     step as ⟨i1, hi1⟩
     unfold lit.Lit.all_of_kind_loop
     have hlt : i1 < 2#usize := by scalar_tac
     simp [hlen, hlt, h1 i1 (by scalar_tac), lit.Lit.kind, litkind_ne_self']
     step as ⟨i2, hi2⟩
     rw [all_of_kind_loop_exit args _ _ i2 (by scalar_tac)]
     simp only [lit.Lit.evaluate_nary, h0, Std.bind_ok, ite_true]
     first
     | (simp [lit.Lit.fold_str, andLit]; done)
     | exact fold_bool_and args _ _ hlen h1
     | exact fold_bv_and args _ _ hlen h1
     | (unfold lit.Lit.fold_int lit.Lit.fold_int_loop
        simp [hlen, h1 1#usize (by simp), lit.Lit.as_int, num.Integer.clone_spec]
        step as ⟨j, hj⟩
        unfold lit.Lit.fold_int_loop
        have hj2 : ¬ j < 2#usize := by scalar_tac
        simp [hlen, hj2, andLit])
     | (unfold lit.Lit.fold_rat lit.Lit.fold_rat_loop
        simp [hlen, h1 1#usize (by simp), lit.Lit.as_rat, num.Rational.clone_spec]
        step as ⟨j, hj⟩
        unfold lit.Lit.fold_rat_loop
        have hj2 : ¬ j < 2#usize := by scalar_tac
        simp [hlen, hj2, andLit]))

/-- The signed value of the `and` of two bit-vectors of width `k`, reduced
modulo `2 ^ k`, is the `and` of their values: logos's `native_piand` takes
`BitVec.toInt`, which is negative where the top bit is set, and the
reduction makes it agree with malachite's `and` of the values. -/
theorem bv_and_toInt_emod (k : Nat) (n1 n2 : Int) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2)
    (h1' : n1 < 2 ^ k) (h2' : n2 < 2 ^ k) :
    ((BitVec.ofInt k n1 &&& BitVec.ofInt k n2).toInt) % (2 ^ k : Int) =
      Int.land n1 n2 % (2 ^ k) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  have ha : a < 2 ^ k := by exact_mod_cast h1'
  have hb : b < 2 ^ k := by exact_mod_cast h2'
  rw [BitVec.toInt_eq_toNat_cond]
  have hn : (BitVec.ofInt k (a : Int) &&& BitVec.ofInt k (b : Int)).toNat = a &&& b := by
    rw [BitVec.toNat_and]
    have e1 : (BitVec.ofInt k (a : Int)).toNat = a := by
      rw [show (a : Int) = ((a : Nat) : Int) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt ha
    have e2 : (BitVec.ofInt k (b : Int)).toNat = b := by
      rw [show (b : Int) = ((b : Nat) : Int) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hb
    rw [e1, e2]
  rw [hn]
  have hl : Int.land (a : Int) (b : Int) = ((a &&& b : Nat) : Int) := rfl
  rw [hl]
  split
  · rfl
  · push_cast
    rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- What a handle of a literal term stands for. -/
theorem Store.rep_lit {s : Store} {a : Term} {x : Eo.Term} {l : lit.Lit}
    (ha : s.Rep a x) (hd : s.nodes.val[a.val]! = TermData.Literal l) :
    (∃ b, x = Eo.Term.Boolean b ∧ l = lit.Lit.Boolean b) ∨
      (∃ i, x = Eo.Term.Numeral i ∧ l = lit.Lit.Numeral (num.Integer.ofInt i)) ∨
      (∃ q, x = Eo.Term.Rational q ∧ l = lit.Lit.Rational (num.Rational.ofRat q)) ∨
      (∃ str, x = Eo.Term.String str ∧ l = lit.Lit.Str (Tree.strOf str)) ∨
      (∃ w n, x = Eo.Term.Binary w n ∧ l = lit.Lit.Binary (Tree.bvOf w n) ∧ Tree.okBv w n) := by
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
    · exact Or.inl ⟨b, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨q, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨str, rfl, rfl⟩)))
    · simp only [Embed.embedded_emb_Term, Embed.emb_Term] at he
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨w, n, rfl, rfl, he⟩)))
  | stuck _ _ hd' => cases hd'.symm.trans hd
  | native _ _ _ hd' => cases hd'.symm.trans hd
  | userop _ _ _ hd' => cases hd'.symm.trans hd
  | apply _ _ _ _ _ _ hd' _ _ => cases hd'.symm.trans hd
  | node _ _ _ _ _ hd' _ => cases hd'.symm.trans hd

theorem Store.rep_boolean_data {s : Store} {a : Term} {b : Bool}
    (ha : s.Rep a (Eo.Term.Boolean b)) :
    s.nodes.val[a.val]! = TermData.Literal (lit.Lit.Boolean b) := by
  obtain ⟨hh, _⟩ := ha
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
  cases hh with
  | lit _ _ _ hd => exact hd

theorem Store.rep_binary_data {s : Store} {a : Term} {w n : Int}
    (ha : s.Rep a (Eo.Term.Binary w n)) :
    s.nodes.val[a.val]! = TermData.Literal (lit.Lit.Binary (Tree.bvOf w n)) := by
  obtain ⟨hh, _⟩ := ha
  simp only [Embed.embedded_enc_Term, Embed.enc_Term] at hh
  cases hh with
  | lit _ _ _ hd => exact hd

/-- `literal` with a binary in range gives a handle of it. -/
theorem Store.literal_binary_spec (s : Store) (w n : Int) (hok : Tree.okBv w n) (hinv : s.Inv)
    (h64 : Platform64) :
    Store.literal s (lit.Lit.Binary (Tree.bvOf w n)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Binary w n)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.literal
  simp only [Std.bind_ok]
  apply WP.dspec_mono (Store.intern_inv s (TermData.Literal (lit.Lit.Binary _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t =>
    refine ⟨?_, by simpa [Embed.embedded_emb_Term, Embed.emb_Term] using hok⟩
    simp only [Embed.embedded_enc_Term, Embed.enc_Term]
    exact Holds.lit t.val _ hres.1 hres.2

/-- `eo::and` of two binaries of the same width, as the runtime computes
it. -/
theorem eo_and_binary (w n1 n2 : Int) (h1 : Tree.okBv w n1) (h2 : Tree.okBv w n2) :
    Eo.__eo_and (Eo.Term.Binary w n1) (Eo.Term.Binary w n2) =
      Eo.Term.Binary w (Int.land n1 n2 % 2 ^ w.toNat) ∧
    Tree.okBv w (Int.land n1 n2 % 2 ^ w.toNat) := by
  obtain ⟨hw0, hw1, hn1, hn1'⟩ := h1
  obtain ⟨-, -, hn2, hn2'⟩ := h2
  have hpos : (0 : Int) < 2 ^ w.toNat := by positivity
  refine ⟨?_, hw0, hw1, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  have hv : SmtEval.native_mod_total (Eo.native_binary_and w n1 n2) (SmtEval.native_int_pow2 w) =
      Int.land n1 n2 % 2 ^ w.toNat := by
    have hp : SmtEval.native_int_pow2 w = 2 ^ w.toNat := by
      simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, show ¬ w < 0 by omega]
    rw [hp]
    simp only [SmtEval.native_mod_total, Eo.native_binary_and, SmtEval.native_ite,
      SmtEval.native_zeq, Eo.native_piand]
    by_cases hw : w = 0
    · subst hw
      simp
    · simp only [hw, decide_false]
      exact bv_and_toInt_emod w.toNat n1 n2 hn1 hn2 hn1' hn2'
  simp [Eo.__eo_and, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not, hv]

theorem Store.builtin_spec_and (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.And args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_and x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.And 2#usize = ok true := by
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
    step with Store.any_stuck_two hargs ha hb as ⟨b1, hb1⟩
    subst hb1
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_and Eo.Term.Stuck y = Eo.Term.Stuck := by simp [Eo.__eo_and]
      rw [this]; exact hinv.rep_stuck
    by_cases hy : y = Eo.Term.Stuck
    · subst hy
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_and x Eo.Term.Stuck = Eo.Term.Stuck := by
        unfold Eo.__eo_and; split <;> simp_all
      rw [this]; exact hinv.rep_stuck
    simp only [hx, hy, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
      kind.EvalOp.is_list_op, Std.bind_ok]
    unfold Store.builtin_literal
    step with Store.literals_two s args hargs ha.lt hb.lt as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_and x y = Eo.Term.Stuck := by
        unfold Eo.__eo_and
        split
        · exact absurd ⟨⟨_, Store.rep_boolean_data ha⟩, ⟨_, Store.rep_boolean_data hb⟩⟩ ho
        · exact absurd ⟨⟨_, Store.rep_binary_data ha⟩, ⟨_, Store.rep_binary_data hb⟩⟩ ho
        · rfl
      rw [this]; exact hinv.rep_stuck
    | some v =>
      obtain ⟨l1, l2, hv, hd1, hd2⟩ := ho
      simp only
      have hx' := Store.rep_lit ha hd1
      have hy' := Store.rep_lit hb hd2
      have ht1 : TermLit l1 := by
        rcases hx' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      have ht2 : TermLit l2 := by
        rcases hy' with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl, _⟩ <;>
          trivial
      step with lit_evaluate_and (alloc.vec.Vec.deref v) (l1 := l1) (l2 := l2)
        (by simp [alloc.vec.Vec.deref, hv]) ht1 ht2 as ⟨o1, ho1⟩
      subst ho1
      rcases hx' with ⟨b1, rfl, rfl⟩ | ⟨i1, rfl, rfl⟩ | ⟨q1, rfl, rfl⟩ | ⟨s1, rfl, rfl⟩ |
          ⟨w1, n1, rfl, rfl, hok1⟩ <;>
        rcases hy' with ⟨b2, rfl, rfl⟩ | ⟨i2, rfl, rfl⟩ | ⟨q2, rfl, rfl⟩ | ⟨s2, rfl, rfl⟩ |
          ⟨w2, n2, rfl, rfl, hok2⟩ <;>
        first
        | (simp only [andLit, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
           exact ⟨hinv, Store.Grows.refl s, by simpa [Eo.__eo_and] using hinv.rep_stuck⟩)
        | (simp only [andLit]
           have he : Eo.__eo_and (Eo.Term.Boolean b1) (Eo.Term.Boolean b2) =
               Eo.Term.Boolean (b1 && b2) := rfl
           rw [he]
           exact Store.literal_boolean_spec s _ hinv h64)
        | (by_cases hw : w1 = w2
           · subst hw
             obtain ⟨he, hok⟩ := eo_and_binary w1 n1 n2 hok1 hok2
             rw [he]
             have hl : andLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w1 n2)) =
                 some (lit.Lit.Binary (Tree.bvOf w1 (Int.land n1 n2 % 2 ^ w1.toNat))) := by
               have hs := Tree.u32Wrap_val w1.toNat (by obtain ⟨_, h, _⟩ := hok1; omega)
               simp [andLit, Tree.bvOf, num.Integer.toInt_ofInt, hs]
               rfl
             rw [hl]
             exact Store.literal_binary_spec s _ _ hok hinv h64
           · have hl : andLit (lit.Lit.Binary (Tree.bvOf w1 n1)) (lit.Lit.Binary (Tree.bvOf w2 n2)) =
                 none := by
               have e1 := Tree.bvW_bvOf w1 n1 hok1
               have e2 := Tree.bvW_bvOf w2 n2 hok2
               simp only [andLit]
               rw [if_neg]
               intro hs; apply hw; unfold Tree.bvW at e1 e2; rw [← e1, ← e2, hs]
             have he : Eo.__eo_and (Eo.Term.Binary w1 n1) (Eo.Term.Binary w2 n2) = Eo.Term.Stuck := by
               simp [Eo.__eo_and, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, hw]
             rw [hl, he]
             simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
             exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩)

end pathos_compiled_checker
