module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import MiniEmbed
public import PathosProofs.Runtime.Compare
public import PathosProofs.Store.Sem

/-!
# `eo::cmp`: `Store::compare` against logos's `termCmp`

`Runtime/Compare.lean` proves that `compare` computes `treeCmp` on the
trees of two handles, given facts about the calculus's tables. Here: those
facts, for the checker's constructors (`order_key_total`,
`of_embedding_total`, `arity_le`), and that on the trees of logos's terms
`treeCmp` is logos's `termCmp` (`treeCmp_enc_Term`), so that `compare` on
two handles standing for terms gives `termCmp` of the terms
(`compare_rep_spec`).

The proofs go by cases on the constructors, with the same tactic for every
case, so that the file holds for any calculus. What the calculus's user
operators need (their keys, logos's order on them) is generated with the
embedding, in the simp set `tree_key`.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result Embed

/-! ## The calculus's tables

By cases on the constructors. `order_key_total` and `arity_le` take about
180,000 heartbeats each for the full CPC's, so close to Lean's default of
200,000 that they get a limit of their own. -/

set_option maxHeartbeats 2000000 in
theorem order_key_total : ∀ c, ∃ p, schema.Constructor.order_key c = ok p := by
  intro c; cases c <;> exact ⟨_, rfl⟩

theorem of_embedding_total : ∀ e, ∃ o, schema.Constructor.of_embedding e = ok o := by
  intro e; cases e <;> exact ⟨_, rfl⟩

set_option maxHeartbeats 2000000 in
theorem arity_le : ∀ c n, schema.Constructor.arity c = ok n → n.val ≤ 100 := by
  have h : ∀ c, ∃ n, schema.Constructor.arity c = ok n ∧ n.val ≤ 100 := by
    intro c; cases c <;> exact ⟨_, rfl, by decide⟩
  intro c n hc
  obtain ⟨m, hm, hle⟩ := h c
  rw [hm] at hc
  obtain rfl := Result.ok_injective hc
  exact hle

/-! ## `treeCmp` on the trees of terms -/

theorem treeCmp_same_key {a b : Tree} {k : Nat × Nat} (ha : treeKey a = some k) (hb : treeKey b = some k) :
    treeCmp a b = bodyCmp a b := by
  rw [treeCmp]; simp [ha, hb]

theorem natCmp_eq (a b : Nat) : Eo.natCmp a b = compare a b := by
  unfold Eo.natCmp
  by_cases h1 : a < b
  · simp [h1, Nat.compare_eq_lt.mpr h1]
  · by_cases h2 : a = b
    · subst h2; simp
    · simp [h1, h2, Nat.compare_eq_gt.mpr (by omega : b < a)]

theorem intCmp_eq (a b : Int) : Eo.intCmp a b = compare a b := by
  unfold Eo.intCmp
  by_cases h1 : a < b
  · simp [h1, Int.compare_eq_lt.mpr h1]
  · by_cases h2 : a = b
    · subst h2; simp
    · simp [h1, h2, Int.compare_eq_gt.mpr (by omega : b < a)]

theorem lexNat_eq : ∀ a b : List Nat, lexNat a b = Eo.stringCmp a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [lexNat, Eo.stringCmp, natCmp_eq]
    by_cases h : x = y
    · subst h; simp [lexNat_eq xs ys]
    · have : compare x y ≠ .eq := by simpa [compare_eq_iff_eq] using h
      simp only [h, ite_false]

theorem compare_natCast (a b : Nat) : compare (a : Int) (b : Int) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | rfl | h
  · rw [Nat.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (by omega)]
  · simp
  · rw [Nat.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (by omega)]

theorem litCmp_str (a b : List Nat) (ha : Tree.okStr a) (hb : Tree.okStr b) :
    litCmp (.Str (Tree.strOf a)) (.Str (Tree.strOf b)) = Eo.stringCmp a b := by
  have h1 := Tree.strTo_strOf a ha
  have h2 := Tree.strTo_strOf b hb
  simp only [Tree.strTo] at h1 h2
  simp only [litCmp, h1, h2, lexNat_eq]

theorem litCmp_int (a b : Int) :
    litCmp (.Numeral (num.Integer.ofInt a)) (.Numeral (num.Integer.ofInt b)) = Eo.intCmp a b := by
  simp [litCmp, num.Integer.toInt_ofInt, intCmp_eq]

theorem litCmp_nat (a b : Nat) :
    litCmp (.Numeral (num.Integer.ofInt a)) (.Numeral (num.Integer.ofInt b)) = Eo.natCmp a b := by
  simp [litCmp, num.Integer.toInt_ofInt, natCmp_eq, compare_natCast]

theorem litCmp_bool (a b : Bool) : litCmp (.Boolean a) (.Boolean b) = Eo.boolCmp a b := by
  cases a <;> cases b <;> rfl

theorem litCmp_rat (a b : ℚ) :
    litCmp (.Rational (num.Rational.ofRat a)) (.Rational (num.Rational.ofRat b)) = Eo.ratCmp a b := by
  simp only [litCmp, num.Rational.toRat_ofRat, Eo.ratCmp, intCmp_eq, natCmp_eq, compare_natCast]
  cases compare a.num b.num <;> rfl

theorem litCmp_bin (w n v m : Int) (h1 : Tree.okBv w n) (h2 : Tree.okBv v m) :
    litCmp (.Binary (Tree.bvOf w n)) (.Binary (Tree.bvOf v m)) =
      match Eo.intCmp w v with
      | .eq => Eo.intCmp n m
      | o => o := by
  have a1 := Tree.bvW_bvOf w n h1
  have a2 := Tree.bvW_bvOf v m h2
  have b1 := Tree.bvV_bvOf w n h1
  have b2 := Tree.bvV_bvOf v m h2
  simp only [Tree.bvW, Tree.bvV] at a1 a2 b1 b2
  simp only [litCmp, intCmp_eq]
  rw [← compare_natCast, a1, a2, b1, b2]
  cases compare w v <;> rfl

theorem then_of_ne_eq {a : Ordering} (b : Ordering) (h : ¬a = .eq) : a.then b = a := by
  cases a <;> simp_all [Ordering.then]

theorem treeCmp_native (l m : lit.Lit) : treeCmp (.native l) (.native m) = litCmp l m := by
  rw [treeCmp]; simp [treeKey, bodyCmp]


-- 76,000 heartbeats for CpcMini, 370,000 for the full CPC
set_option maxHeartbeats 2000000 in
/-- The order `Store::compare` computes on the trees of logos's terms is
logos's `termCmp`: by the mutual recursor, the cases of two different
constructors by computing both sides (their keys are the constructors'
indices, in the same order), the others field by field. -/
theorem treeCmp_enc_Term : ∀ x : Eo.Term, ∀ y, emb_Term x → emb_Term y →
    treeCmp (enc_Term x) (enc_Term y) = Eo.termCmp x y := by
  apply Eo.Term.rec
    (motive_1 := fun x => ∀ y, emb_Term x → emb_Term y →
      treeCmp (enc_Term x) (enc_Term y) = Eo.termCmp x y)
    (motive_2 := fun d => ∀ e, emb_DatatypeDecl d → emb_DatatypeDecl e →
      treeCmp (enc_DatatypeDecl d) (enc_DatatypeDecl e) = Eo.datatypeDeclCmp d e)
    (motive_3 := fun d => ∀ e, emb_Datatype d → emb_Datatype e →
      treeCmp (enc_Datatype d) (enc_Datatype e) = Eo.datatypeCmp d e)
    (motive_4 := fun d => ∀ e, emb_DatatypeCons d → emb_DatatypeCons e →
      treeCmp (enc_DatatypeCons d) (enc_DatatypeCons e) = Eo.datatypeConsCmp d e)
  all_goals (intros; rename_i y hx hy; cases y)
  all_goals (first
    | (rw [treeCmp]; rfl)
    | (rw [treeCmp_same_key rfl rfl]
       simp only [enc_Term, enc_DatatypeDecl, enc_Datatype, enc_DatatypeCons, bodyCmp] at hx hy ⊢)
    | (rw [treeCmp]
       simp only [enc_Term, treeKey, tree_key]
       try rfl))
  all_goals (simp only [emb_Term, emb_DatatypeDecl, emb_Datatype, emb_DatatypeCons] at hx hy)
  all_goals (simp_all [listCmp, litCmp_bool, litCmp_int, litCmp_rat, litCmp_str, litCmp_bin,
      Eo.termCmp, Eo.datatypeDeclCmp, Eo.datatypeCmp, Eo.datatypeConsCmp, natCmp_eq, tree_key,
      intCmp_eq, treeCmp_native, compare_natCast, Tree.encStr, Tree.encNat])
  all_goals (try unfold Ordering.then)
  all_goals ((repeat' split) <;> simp_all [bodyCmp, listCmp, then_of_ne_eq])

/-! ## `compare` on handles of terms -/

/-- `compare` on two handles that stand for terms gives logos's order on
the terms. -/
theorem compare_rep_spec (s : Store) (hinv : s.Inv) (h64 : Platform64)
    (a b : Term) {x y : Eo.Term} (ha : s.Rep a x) (hb : s.Rep b y) :
    Store.compare s a b ⦃ r => ∀ o, r = core.result.Result.Ok o → o = Eo.termCmp x y ⦄div := by
  have h := compare_spec s hinv h64 100 (by decide) (by decide) arity_le order_key_total
    of_embedding_total a b ha.1 hb.1
  have he := treeCmp_enc_Term x y ha.2 hb.2
  simp only [embedded_enc_Term] at h
  rw [he] at h
  exact h

end pathos_compiled_checker
