module
public import MiniChecker
public import CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem

/-!
# What every generated program does around its body

A generated program is `enter`, its body, `leave`: `enter` counts the call
and the depth and refuses past the limits, `leave` gives the depth back.
Neither touches the terms. Also here: the small facts about the Rust that
every body uses (the comparison of two handles, the empty argument list).
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The invariant is about the terms and their table only. -/
theorem Store.Inv.congr {s s' : Store} (h : s.Inv) (hn : s'.nodes = s.nodes)
    (hh : s'.hashes = s.hashes) (hs : s'.slots = s.slots) (hc : s'.caches = s.caches) :
    s'.Inv := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [hn, hh, hs, hc] <;> assumption

/-- `enter` counts a call: the terms are as they were, the depth one more. -/
theorem Store.enter_spec (s : Store) :
    Store.enter s ⦃ r s' =>
      s'.nodes = s.nodes ∧ s'.hashes = s.hashes ∧ s'.slots = s.slots ∧
      s'.caches = s.caches ∧ s'.limits = s.limits ∧
      match r with
      | core.result.Result.Ok _ => s'.depth.val = s.depth.val + 1
      | core.result.Result.Err _ => s'.depth = s.depth ⦄ := by
  unfold Store.enter
  split
  · simp
  · split
    · simp
    · step*

/-- `leave` gives the depth back. -/
theorem Store.leave_spec (s : Store) (h : 0 < s.depth.val) :
    Store.leave s ⦃ s' =>
      s'.nodes = s.nodes ∧ s'.hashes = s.hashes ∧ s'.slots = s.slots ∧
      s'.caches = s.caches ∧ s'.limits = s.limits ∧ s'.depth.val = s.depth.val - 1 ⦄ := by
  unfold Store.leave
  step*

/-- `!=` on two handles. -/
theorem Term.ne_eq (a b : Term) :
    core.cmp.PartialEq.ne.trait_default Term.Insts.CoreCmpPartialEqTerm a b
      = ok (decide (a ≠ b)) := by
  have hEq : Term.Insts.CoreCmpPartialEqTerm.eq a b ⦃ r => r ↔ (a = b) ⦄ := by
    simp [Term.Insts.CoreCmpPartialEqTerm.eq]
  obtain ⟨r, hr, hiff⟩ := spec_returns
    (core.cmp.PartialEq.ne.trait_default.spec Term.Insts.CoreCmpPartialEqTerm a b hEq)
  rw [hr]
  congr 1
  cases r <;> simp_all

/-- A store with the same terms stands for the same terms. -/
theorem Store.Rep.congr {s s' : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x)
    (hn : s'.nodes = s.nodes) : s'.Rep t x := by
  unfold Store.Rep at h ⊢
  rw [hn]; exact h

/-- A generated program is `enter`, its body and `leave`: what holds of the
body holds of the program. -/
theorem Store.framed {α : Type} (s : Store) (hinv : s.Inv)
    (body : Store → Result ((core.result.Result α CheckError) × Store))
    (post : Store → α → Prop)
    (hpost : ∀ (s1 s2 : Store) (a : α), s2.nodes = s1.nodes → post s1 a → post s2 a)
    (hbody : ∀ s1 : Store, s1.Inv → s1.nodes = s.nodes →
      body s1 ⦃ r s2 => s2.Inv ∧ s1.Grows s2 ∧
        match r with
        | core.result.Result.Ok a => post s2 a
        | core.result.Result.Err _ => True ⦄div) :
    (do
      let (r, s1) ← Store.enter s
      match r with
      | core.result.Result.Ok _ =>
        let (result, s2) ← body s1
        let s3 ← Store.leave s2
        ok (result, s3)
      | core.result.Result.Err e => ok (core.result.Result.Err e, s1)) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok a => post s' a
      | core.result.Result.Err _ => True ⦄div := by
  step with Store.enter_spec as ⟨r, s1, hn, hh, hs, hc, hl, hd⟩
  have hinv1 : s1.Inv := hinv.congr hn hh hs hc
  cases r with
  | Err e =>
    simp only [WP.dspec_ok, WP.uncurry'_pair] at hd ⊢
    exact ⟨hinv1, ⟨by rw [hn], hl, hd⟩, trivial⟩
  | Ok u =>
    simp only at hd ⊢
    step with hbody s1 hinv1 hn as ⟨result, s2, hinv2, hg2, hres⟩
    have hdepth : 0 < s2.depth.val := by rw [hg2.depth, hd]; omega
    step with Store.leave_spec as ⟨s3, hn3, hh3, hs3, hc3, hl3, hd3⟩
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    refine ⟨hinv2.congr hn3 hh3 hs3 hc3, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hn3, ← hn]; exact hg2.nodes
    · rw [hl3, hg2.limits, hl]
    · have : s3.depth.val = s.depth.val := by rw [hd3, hg2.depth, hd]; omega
      scalar_tac
    · cases result with
      | Err e => trivial
      | Ok a => exact hpost s2 s3 a hn3 hres

end pathos_compiled_checker
