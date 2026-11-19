module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Trusted

/-!
# `same_data` is equality

The table of terms compares the data of two terms with `Store.same_data`,
which is written out in the runtime (the derived `==` on a term's data is
not in the subset that is translated). This file proves that it answers
`true` exactly when the two are equal, from the equality of the numbers
that `Trusted.lean` states.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

theorem num.Integer.toInt_inj {a b : num.Integer} : a.toInt = b.toInt ↔ a = b := by
  constructor
  · intro h
    rw [← num.Integer.ofInt_toInt a, ← num.Integer.ofInt_toInt b, h]
  · intro h; rw [h]

theorem num.Rational.toRat_inj {a b : num.Rational} : a.toRat = b.toRat ↔ a = b := by
  constructor
  · intro h
    rw [← num.Rational.ofRat_toRat a, ← num.Rational.ofRat_toRat b, h]
  · intro h; rw [h]

@[step]
theorem num.Integer.eq_iff (a b : num.Integer) :
    num.Integer.Insts.CoreCmpPartialEqInteger.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  rw [num.Integer.eq_spec]
  simp [num.Integer.toInt_inj]

@[step]
theorem num.Rational.eq_iff (a b : num.Rational) :
    num.Rational.Insts.CoreCmpPartialEqRational.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  rw [num.Rational.eq_spec]
  simp [num.Rational.toRat_inj]

@[step]
theorem bitvec.BitVec.eq_iff (a b : bitvec.BitVec) :
    bitvec.BitVec.Insts.CoreCmpPartialEqBitVec.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold bitvec.BitVec.Insts.CoreCmpPartialEqBitVec.eq
  split
  · rename_i h
    step as ⟨r, hr⟩
    rw [hr]
    cases a; cases b; simp_all
  · rename_i h
    simp only [WP.spec_ok]
    constructor
    · intro hf; simp at hf
    · intro heq; subst heq; exact absurd rfl h

theorem allM_zip_u32 (l1 l2 : List Std.U32) (h : l1.length = l2.length) :
    List.allM (fun (x : Std.U32 × Std.U32) => liftFun2 core.cmp.impls.PartialEqU32.eq x.1 x.2)
        (List.zip l1 l2)
      = ok (decide (l1 = l2)) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp only [List.zip_nil_left, List.allM_nil, decide_true]; rfl
    | cons b bs => simp at h
  | cons a rest ih =>
    cases l2 with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zip_cons_cons, List.allM_cons]
      have hab : liftFun2 core.cmp.impls.PartialEqU32.eq a b = ok (decide (a = b)) := rfl
      rw [hab]
      simp only [bind_tc_ok]
      by_cases heq : a = b
      · subst heq
        simp at h
        simp [ih bs h]
      · simp [heq]; rfl

@[step]
theorem eostring.EoString.eq_iff (a b : eostring.EoString) :
    eostring.EoString.Insts.CoreCmpPartialEqEoString.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold eostring.EoString.Insts.CoreCmpPartialEqEoString.eq
    alloc.vec.partial_eq.PartialEqVec.eq
  split
  · rename_i h
    have := allM_zip_u32 a.val b.val h
    rw [this]
    simp only [WP.spec_ok, decide_eq_true_eq]
    constructor
    · intro hv; exact alloc.vec.Vec.ext _ _ hv
    · intro hv; rw [hv]
  · rename_i h
    simp only [WP.spec_ok]
    constructor
    · intro hf; simp at hf
    · intro heq; subst heq; exact absurd rfl h

@[step]
theorem lit.Lit.eq_iff (a b : lit.Lit) :
    lit.Lit.Insts.CoreCmpPartialEqLit.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold lit.Lit.Insts.CoreCmpPartialEqLit.eq
  cases a <;> cases b <;> simp [read_discriminant] <;> first
    | (step as ⟨r, hr⟩; exact hr)
    | simp [core.cmp.impls.PartialEqBool.eq]

deriving instance DecidableEq for schema.Constructor

/-- A constructor's code is its number among the constructors. -/
theorem schema.Constructor.code_spec (c : schema.Constructor) :
    ∃ n : Std.U32, c.code = ok n ∧ n.val = c.ctorIdx := by
  cases c <;> exact ⟨_, rfl, rfl⟩

theorem schema.Constructor.code_inj {c d : schema.Constructor} {n : Std.U32}
    (hc : c.code = ok n) (hd : d.code = ok n) : c = d := by
  obtain ⟨n1, h1, e1⟩ := schema.Constructor.code_spec c
  obtain ⟨n2, h2, e2⟩ := schema.Constructor.code_spec d
  rw [hc] at h1; rw [hd] at h2
  have h1' : n = n1 := by simpa using h1
  have h2' : n = n2 := by simpa using h2
  subst h1'; subst h2'
  rw [← schema.Constructor.ofNat_ctorIdx c, ← schema.Constructor.ofNat_ctorIdx d, ← e1, ← e2]

theorem Store.same_terms_loop_spec (a b : Slice Term) (hlen : a.length = b.length)
    (same : Bool) (i : Std.Usize) :
    Store.same_terms_loop a b same i ⦃ r =>
      (r = true ↔ same = true ∧ ∀ j : Nat, i.val ≤ j → j < a.length → a.val[j]! = b.val[j]!) ⦄div := by
  revert same i
  apply Store.same_terms_loop.fixpoint_induct a b
    (motive := fun f => ∀ (same : Bool) (i : Std.Usize),
      f same i ⦃ r =>
        (r = true ↔ same = true ∧ ∀ j : Nat, i.val ≤ j → j < a.length → a.val[j]! = b.val[j]!) ⦄div)
  · prove_adm
  · intro loop ih same i
    simp only
    split
    · rename_i hlt
      step as ⟨t, ht⟩
      step as ⟨t1, ht1⟩
      have hilt : i.val < a.val.length := by scalar_tac
      have hilt' : i.val < b.val.length := by scalar_tac
      have hta : a.val[i.val]! = t := by rw [ht]; exact getElem!_eq _ _ hilt
      have htb : b.val[i.val]! = t1 := by rw [ht1]; exact getElem!_eq _ _ hilt'
      split
      · rename_i hne
        step as ⟨i2, hi2⟩
        step with ih as ⟨r, hr⟩
        rw [hr]
        constructor
        · intro h; simp at h
        · intro ⟨_, h⟩
          have := h i.val (le_refl _) hilt
          rw [hta, htb] at this
          simp [this] at hne
      · rename_i heq
        step as ⟨i2, hi2⟩
        step with ih as ⟨r, hr⟩
        rw [hr]
        have heq' : t = t1 := by simp at heq; scalar_tac
        constructor
        · intro ⟨hs, h⟩
          refine ⟨hs, ?_⟩
          intro j hj hjl
          by_cases hji : j = i.val
          · subst hji; rw [hta, htb, heq']
          · exact h j (by omega) hjl
        · intro ⟨hs, h⟩
          exact ⟨hs, fun j hj hjl => h j (by omega) hjl⟩
    · rename_i hge
      simp only [WP.dspec_ok]
      constructor
      · intro h
        refine ⟨h, ?_⟩
        intro j hj hjl
        exfalso; scalar_tac
      · intro ⟨h, _⟩; exact h

@[step]
theorem Store.same_terms_spec (a b : Slice Term) :
    Store.same_terms a b ⦃ r => (r = true ↔ a = b) ⦄div := by
  unfold Store.same_terms
  dsimp only
  split
  · rename_i hne
    simp only [WP.dspec_ok]
    constructor
    · intro h; simp at h
    · intro h; subst h; simp at hne
  · rename_i heq
    have hlen : a.length = b.length := by
      simp at heq; scalar_tac
    step with Store.same_terms_loop_spec as ⟨r, hr⟩
    rw [hr]
    constructor
    · intro h
      apply Slice.ext
      apply List.ext_getElem! hlen
      intro j
      by_cases hj : j < a.length
      · exact h j (by simp) hj
      · have hj' : ¬ j < b.val.length := by simp only [Slice.length] at hlen hj; omega
        have hj'' : ¬ j < a.val.length := by simp only [Slice.length] at hj; omega
        simp [hj'', hj']
    · intro h; subst h; simp

/-- `same_data` answers `true` exactly on equal data. -/
theorem Store.same_data_spec (a b : TermData) :
    Store.same_data a b ⦃ r => (r = true ↔ a = b) ⦄div := by
  unfold Store.same_data
  cases a <;> cases b <;> simp only [WP.dspec_ok, reduceCtorEq, Bool.false_eq_true, iff_self,
    TermData.Literal.injEq, TermData.Native.injEq, TermData.UserOp.injEq, TermData.Apply.injEq,
    TermData.Node.injEq]
  · step as ⟨r, hr⟩; exact hr
  · step as ⟨r, hr⟩; exact hr
  · rename_i c d
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec c
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    rw [h1, h2]
    simp
    constructor
    · intro h; subst h; exact schema.Constructor.code_inj h1 h2
    · intro h; subst h; rw [h1] at h2; simpa using h2
  · rename_i f x g y
    split
    · rename_i h; subst h; simp
    · rename_i h; simp [h]
  · rename_i c xs d ys
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec c
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    rw [h1, h2]
    simp
    split
    · rename_i h; subst h
      have hcd : c = d := schema.Constructor.code_inj h1 h2
      step as ⟨r, hr⟩
      rw [hr]
      constructor
      · intro h; refine ⟨hcd, ?_⟩
        apply alloc.vec.Vec.ext
        have := congrArg Slice.val h
        simpa [alloc.vec.Vec.deref] using this
      · intro ⟨_, h⟩; rw [h]
    · rename_i h
      simp only [WP.dspec_ok, Bool.false_eq_true, false_iff]
      intro ⟨hcd, _⟩
      subst hcd
      rw [h1] at h2
      apply h; simpa using h2

end pathos_compiled_checker
