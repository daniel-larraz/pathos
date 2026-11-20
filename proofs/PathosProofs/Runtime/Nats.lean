module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops

/-!
# The native natural numbers: `nat.zero` and the `nat.zero`/`nat.succ` patterns

logos's natural numbers (`native_nat_zero`, `native_nat_succ`, which are
`Nat.zero` and `Nat.succ`) are stored as native numerals: the natural `n`
is the `Integer` `ofInt n` (`Tree.encNat`). The constant `nat.zero` is
`Integer::zero()`; the pattern `nat.zero` compares a handle with the
handle of that constant; the pattern `(nat.succ m)` reads the numeral
(`raw_int`, a clone), tests its sign, and stores the numeral less one
(`add` of `neg` of `one`). Both patterns store a numeral, so they change
the store, as the pattern on a Boolean literal does.

These rest on `Trusted.lean`'s `Integer.zero_spec`, `one_spec`,
`clone_spec`, `sgn_spec`, `neg_spec` and `add_spec`: what malachite's
integers compute, through `num.rs`.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `raw` of the numeral of a natural number gives a handle of it. -/
theorem Store.raw_nat_spec (s : Store) (n : Nat) (hinv : s.Inv) (h64 : Platform64) :
    Store.raw s (lit.Lit.Numeral (num.Integer.ofInt n)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t n
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Numeral _)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact ⟨Holds.native t.val _ hres.1 hres.2, trivial⟩

/-- The constant `nat.zero` gives a handle of `0`. -/
theorem Store.native_nat_zero_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_nat_zero s ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (0 : Nat)
      | core.result.Result.Err _ => True ⦄div := by
  unfold native.Store.native_nat_zero
  rw [num.Integer.zero_spec]
  simp only [Std.bind_ok]
  have := Store.raw_nat_spec s 0 hinv h64
  simpa using this

/-- What a handle of a natural number stands for in the store: its
numeral. -/
theorem Store.rep_nat_data {s : Store} {t : Term} {x : Nat} (h : Represents.rep s t x) :
    t.val < s.nodes.length ∧
      s.nodes.val[t.val]! = TermData.Native (lit.Lit.Numeral (num.Integer.ofInt x)) := by
  obtain ⟨hh, _⟩ := h
  simp only [Tree.embedded_enc_Nat, Tree.encNat] at hh
  cases hh with
  | native _ _ hlt hd => exact ⟨hlt, hd⟩

/-- The pattern `nat.zero`: no fields where the natural number is `0`,
nothing for any other. -/
theorem Store.native_pattern_nat_zero_spec (s : Store) (t : Term) {x : Nat}
    (h : Represents.rep s t x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_pattern_nat_zero s t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) => x = 0 ∧ v.val = []
      | core.result.Result.Ok none => x ≠ 0
      | core.result.Result.Err _ => True ⦄div := by
  unfold native.Store.native_pattern_nat_zero
  step with Store.native_nat_zero_spec s hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv1, hg1⟩
  | Ok z =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      native.Store.pattern_constant, Term.Insts.CoreCmpPartialEqTerm.eq]
    have h1 := Represents.grows h hg1
    have hiff := Represents.eq_iff hinv1 hr h1
    by_cases hz : z = t
    · simp only [hz, decide_true, ite_true, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, (hiff.mp hz).symm, rfl⟩
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      exact ⟨hinv1, hg1, fun hx => hz (hiff.mpr hx.symm)⟩

/-- The pattern `(nat.succ m)`: a handle of the predecessor where the
natural number is a successor, nothing where it is `0`. -/
theorem Store.native_pattern_succ_spec (s : Store) (t : Term) {x : Nat}
    (h : Represents.rep s t x) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_pattern_succ s t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (f : Term) (m : Nat), x = m + 1 ∧ v.val = [f] ∧ Represents.rep s' f m
      | core.result.Result.Ok none => ∀ m : Nat, x ≠ m + 1
      | core.result.Result.Err _ => True ⦄div := by
  obtain ⟨hlt, hd⟩ := Store.rep_nat_data h
  unfold native.Store.native_pattern_succ Store.raw_int
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hd,
    num.Integer.clone_spec]
  obtain ⟨sg, hsg, hsv⟩ := num.Integer.sgn_spec (num.Integer.ofInt x)
  rw [hsg]
  simp only [Std.bind_ok]
  rw [num.Integer.toInt_ofInt] at hsv
  by_cases hx : x = 0
  · subst hx
    have : ¬ (sg > 0#i32) := by
      intro hgt
      have : (0 : Int) < sg.val := by scalar_tac
      simp at hsv; omega
    simp only [this, ite_false, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, fun m hm => by omega⟩
  · have hpos : sg > 0#i32 := by
      have : (0 : Int) < (x : Int) := by omega
      have : sg.val = 1 := by rw [hsv]; exact Int.sign_eq_one_of_pos this
      scalar_tac
    simp only [hpos, ite_true, num.Integer.one_spec, num.Integer.neg_spec,
      num.Integer.add_spec, num.Integer.toInt_ofInt, Std.bind_ok]
    obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
    have hcast : ((m + 1 : Nat) : Int) + -1 = ((m : Nat) : Int) := by push_cast; ring
    rw [hcast]
    step with Store.raw_nat_spec s m hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact ⟨hinv1, hg1⟩
    | Ok f =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift,
        WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv1, hg1, f, m, rfl, ?_, hr⟩
      simp [alloc.slice.Slice.into_vec, Std.Array.to_slice, Array.make]
      rfl

end pathos_compiled_checker
