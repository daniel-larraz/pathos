module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Programs.Frame

/-!
# `$mk_symm`: a program that is not recursive

The generated `eo__24mk_5fsymm` computes logos's `__mk_symm`: on a handle
of a term `x` it returns a handle of `__mk_symm x`.

The program has two cases, each a function that answers `Some` of its
result when its pattern matches and `None` when it does not. A case is
specified by what it answers in both events; the body then is the first
case that matches, which is how logos's definition by cases reads.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The empty list of arguments, as the generated code writes `&[]`. -/
theorem empty_args : (Array.to_slice (Std.Array.empty Term)).val = [] := rfl

/-- First case: `(= t1 t2)` gives `(= t2 t1)`. -/
theorem generated.part0.case_0_eo__24mk_5fsymm_spec (s : Store) (a0 : Term) (x : Eo.Term)
    (hinv : s.Inv) (h64 : Platform64) (hx : s.Rep a0 x) :
    generated.part0.case_0_eo__24mk_5fsymm s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ t1 t2, x = Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t1) t2 ∧
          s'.Rep t (Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t2) t1)
      | core.result.Result.Ok none =>
        ∀ t1 t2, x ≠ Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t1) t2
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_0_eo__24mk_5fsymm
  rcases hx.unapply with ⟨v1, v2, x1, x2, rfl, h1, h2, hu⟩ | ⟨hne, hu⟩
  · rw [hu]
    simp only [Std.bind_ok, uncurry_apply_pair]
    rcases h1.unapply with ⟨v4, v5, y1, y2, rfl, h4, h5, hu1⟩ | ⟨hne1, hu1⟩
    · rw [hu1]
      simp only [Std.bind_ok, uncurry_apply_pair]
      obtain ⟨hx1ns, hx2ns⟩ := Store.Rep.apply_ne_stuck hinv hx
      obtain ⟨hy1ns, hy2ns⟩ := Store.Rep.apply_ne_stuck hinv h1
      step as ⟨s1, hs1⟩
      step with Store.construct_uop_spec s Eo.UserOp.eq s1 (by rw [hs1]; exact empty_args)
        hinv h64 as ⟨r2, s2, hinv2, hg2, hr2⟩
      cases r2 with
      | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg2, trivial⟩
      | Ok v6 =>
        simp only at hr2 ⊢
        rw [Term.ne_eq]
        simp only [Std.bind_ok]
        have hiff := Store.Rep.eq_iff hinv2 (h4.grows hg2) hr2
        by_cases hv : v4 = v6
        · have hdec : decide (v4 ≠ v6) = false := by simp [hv]
          rw [hdec]
          simp only [Bool.false_eq_true, ite_false]
          have hy1 : y1 = Eo.Term.UOp Eo.UserOp.eq := hiff.mp hv
          subst hy1
          step as ⟨s3, hs3⟩
          step with Store.construct_uop_spec s2 Eo.UserOp.eq s3 (by rw [hs3]; exact empty_args)
            hinv2 h64 as ⟨r3, s4, hinv4, hg4, hr3⟩
          cases r3 with
          | Err e =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv4, hg2.trans hg4, trivial⟩
          | Ok v7 =>
            simp only at hr3 ⊢
            step with Store.apply_rep s4 v7 v2 (Eo.Term.UOp Eo.UserOp.eq) x2 hinv4 h64 hr3
              (h2.grows (hg2.trans hg4)) (by simp) hx2ns as ⟨r4, s5, hinv5, hg5, hr4⟩
            cases r4 with
            | Err e =>
              simp only [WP.dspec_ok, WP.uncurry'_pair]
              exact ⟨hinv5, (hg2.trans hg4).trans hg5, trivial⟩
            | Ok v8 =>
              simp only at hr4 ⊢
              step with Store.apply_rep s5 v8 v5 _ y2 hinv5 h64 hr4
                (h5.grows ((hg2.trans hg4).trans hg5)) (by simp) hy2ns
                as ⟨r5, s6, hinv6, hg6, hr5⟩
              cases r5 with
              | Err e =>
                simp only [WP.dspec_ok, WP.uncurry'_pair]
                exact ⟨hinv6, ((hg2.trans hg4).trans hg5).trans hg6, trivial⟩
              | Ok v9 =>
                simp only [WP.dspec_ok, WP.uncurry'_pair] at hr5 ⊢
                exact ⟨hinv6, ((hg2.trans hg4).trans hg5).trans hg6, y2, x2, rfl, hr5⟩
        · have hdec : decide (v4 ≠ v6) = true := by simp [hv]
          rw [hdec]
          simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv2, hg2, ?_⟩
          intro t1 t2 heq
          injection heq with heq1 _
          injection heq1 with heq2 _
          exact hv (hiff.mpr heq2)
    · rw [hu1]
      simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      intro t1 t2 heq
      injection heq with heq1 _
      exact hne1 _ _ heq1
  · rw [hu]
    simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, fun t1 t2 heq => hne _ _ heq⟩

/-- Second case: `(not (= t1 t2))` gives `(not (= t2 t1))`. -/
theorem generated.part0.case_1_eo__24mk_5fsymm_spec (s : Store) (a0 : Term) (x : Eo.Term)
    (hinv : s.Inv) (h64 : Platform64) (hx : s.Rep a0 x) :
    generated.part0.case_1_eo__24mk_5fsymm s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ t1 t2, x = Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not)
            (Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t1) t2) ∧
          s'.Rep t (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not)
            (Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t2) t1))
      | core.result.Result.Ok none =>
        ∀ t1 t2, x ≠ Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not)
            (Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t1) t2)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_1_eo__24mk_5fsymm
  rcases hx.unapply with ⟨v1, v2, x1, x2, rfl, h1, h2, hu⟩ | ⟨hne, hu⟩
  · rw [hu]
    simp only [Std.bind_ok, uncurry_apply_pair]
    step as ⟨a1, ha1⟩
    step with Store.construct_uop_spec s Eo.UserOp.not a1 (by rw [ha1]; exact empty_args)
      hinv h64 as ⟨r1, s2, hinv2, hg2, hr1⟩
    cases r1 with
    | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg2, trivial⟩
    | Ok v3 =>
      simp only at hr1 ⊢
      rw [Term.ne_eq]
      simp only [Std.bind_ok]
      have hiff := Store.Rep.eq_iff hinv2 (h1.grows hg2) hr1
      by_cases hv : v1 = v3
      · have hdec : decide (v1 ≠ v3) = false := by simp [hv]
        rw [hdec]
        simp only [Bool.false_eq_true, ite_false]
        have hx1 : x1 = Eo.Term.UOp Eo.UserOp.not := hiff.mp hv
        subst hx1
        have h2' := h2.grows hg2
        rcases h2'.unapply with ⟨v5, v6, z1, z2, rfl, h5, h6, hu2⟩ | ⟨hne2, hu2⟩
        · rw [hu2]
          simp only [Std.bind_ok, uncurry_apply_pair]
          rcases h5.unapply with ⟨v8, v9, w1, w2, rfl, h8, h9, hu3⟩ | ⟨hne3, hu3⟩
          · rw [hu3]
            simp only [Std.bind_ok, uncurry_apply_pair]
            obtain ⟨_, hz2ns⟩ := Store.Rep.apply_ne_stuck hinv2 h2'
            obtain ⟨_, hw2ns⟩ := Store.Rep.apply_ne_stuck hinv2 h5
            step as ⟨a3, ha3⟩
            step with Store.construct_uop_spec s2 Eo.UserOp.eq a3 (by rw [ha3]; exact empty_args)
              hinv2 h64 as ⟨r4, s4, hinv4, hg4, hr4⟩
            cases r4 with
            | Err e =>
              simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv4, hg2.trans hg4, trivial⟩
            | Ok v10 =>
              simp only at hr4 ⊢
              rw [Term.ne_eq]
              simp only [Std.bind_ok]
              have hiff2 := Store.Rep.eq_iff hinv4 (h8.grows hg4) hr4
              by_cases hv2 : v8 = v10
              · have hdec2 : decide (v8 ≠ v10) = false := by simp [hv2]
                rw [hdec2]
                simp only [Bool.false_eq_true, ite_false]
                have hw1 : w1 = Eo.Term.UOp Eo.UserOp.eq := hiff2.mp hv2
                subst hw1
                step as ⟨a5, ha5⟩
                step with Store.construct_uop_spec s4 Eo.UserOp.not a5
                  (by rw [ha5]; exact empty_args) hinv4 h64 as ⟨r5, s6, hinv6, hg6, hr5⟩
                cases r5 with
                | Err e =>
                  simp only [WP.dspec_ok, WP.uncurry'_pair]
                  exact ⟨hinv6, (hg2.trans hg4).trans hg6, trivial⟩
                | Ok v11 =>
                  simp only at hr5 ⊢
                  step as ⟨a7, ha7⟩
                  step with Store.construct_uop_spec s6 Eo.UserOp.eq a7
                    (by rw [ha7]; exact empty_args) hinv6 h64 as ⟨r6, s8, hinv8, hg8, hr6⟩
                  cases r6 with
                  | Err e =>
                    simp only [WP.dspec_ok, WP.uncurry'_pair]
                    exact ⟨hinv8, ((hg2.trans hg4).trans hg6).trans hg8, trivial⟩
                  | Ok v12 =>
                    simp only at hr6 ⊢
                    step with Store.apply_rep s8 v12 v6 (Eo.Term.UOp Eo.UserOp.eq) z2 hinv8 h64 hr6
                      (h6.grows ((hg4.trans hg6).trans hg8)) (by simp) hz2ns
                      as ⟨r7, s9, hinv9, hg9, hr7⟩
                    cases r7 with
                    | Err e =>
                      simp only [WP.dspec_ok, WP.uncurry'_pair]
                      exact ⟨hinv9, (((hg2.trans hg4).trans hg6).trans hg8).trans hg9, trivial⟩
                    | Ok v13 =>
                      simp only at hr7 ⊢
                      step with Store.apply_rep s9 v13 v9 _ w2 hinv9 h64 hr7
                        (h9.grows (((hg4.trans hg6).trans hg8).trans hg9)) (by simp) hw2ns
                        as ⟨r8, s10, hinv10, hg10, hr8⟩
                      cases r8 with
                      | Err e =>
                        simp only [WP.dspec_ok, WP.uncurry'_pair]
                        exact ⟨hinv10,
                          ((((hg2.trans hg4).trans hg6).trans hg8).trans hg9).trans hg10, trivial⟩
                      | Ok v14 =>
                        simp only at hr8 ⊢
                        step with Store.apply_rep s10 v11 v14 (Eo.Term.UOp Eo.UserOp.not) _ hinv10 h64
                          (hr5.grows ((hg8.trans hg9).trans hg10)) hr8 (by simp) (by simp)
                          as ⟨r9, s11, hinv11, hg11, hr9⟩
                        cases r9 with
                        | Err e =>
                          simp only [WP.dspec_ok, WP.uncurry'_pair]
                          exact ⟨hinv11, (((((hg2.trans hg4).trans hg6).trans hg8).trans hg9).trans
                            hg10).trans hg11, trivial⟩
                        | Ok v15 =>
                          simp only [WP.dspec_ok, WP.uncurry'_pair] at hr9 ⊢
                          exact ⟨hinv11, (((((hg2.trans hg4).trans hg6).trans hg8).trans hg9).trans
                            hg10).trans hg11, w2, z2, rfl, hr9⟩
              · have hdec2 : decide (v8 ≠ v10) = true := by simp [hv2]
                rw [hdec2]
                simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
                refine ⟨hinv4, hg2.trans hg4, ?_⟩
                intro t1 t2 heq
                injection heq with _ heq1
                injection heq1 with heq2 _
                injection heq2 with heq3 _
                exact hv2 (hiff2.mpr heq3)
          · rw [hu3]
            simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv2, hg2, ?_⟩
            intro t1 t2 heq
            injection heq with _ heq1
            injection heq1 with heq2 _
            exact hne3 _ _ heq2
        · rw [hu2]
          simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv2, hg2, ?_⟩
          intro t1 t2 heq
          injection heq with _ heq1
          exact hne2 _ _ heq1
      · have hdec : decide (v1 ≠ v3) = true := by simp [hv]
        rw [hdec]
        simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv2, hg2, ?_⟩
        intro t1 t2 heq
        injection heq with heq1 _
        exact hv (hiff.mpr heq1)
  · rw [hu]
    simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, fun t1 t2 heq => hne _ _ heq⟩

/-- The body: the first case that matches, as logos's definition by cases. -/
theorem generated.part0.body_eo__24mk_5fsymm_spec (s : Store) (a0 : Term) (x : Eo.Term)
    (hinv : s.Inv) (h64 : Platform64) (hx : s.Rep a0 x) :
    generated.part0.body_eo__24mk_5fsymm s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__mk_symm x)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.body_eo__24mk_5fsymm
  rw [hx.is_stuck]
  simp only [Std.bind_ok]
  by_cases hxs : x = Eo.Term.Stuck
  · subst hxs
    simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    refine ⟨hinv, Store.Grows.refl s, ?_⟩
    have : Eo.__mk_symm Eo.Term.Stuck = Eo.Term.Stuck := by simp [Eo.__mk_symm]
    rw [this]; exact hinv.rep_stuck
  · simp only [hxs, decide_false, Bool.false_eq_true, ite_false]
    step with generated.part0.case_0_eo__24mk_5fsymm_spec s a0 x hinv h64 hx
      as ⟨r1, s1, hinv1, hg1, hr1⟩
    cases r1 with
    | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
    | Ok o1 =>
      cases o1 with
      | some found =>
        simp only [WP.dspec_ok, WP.uncurry'_pair] at hr1 ⊢
        obtain ⟨t1, t2, rfl, hrep⟩ := hr1
        refine ⟨hinv1, hg1, ?_⟩
        simpa [Eo.__mk_symm] using hrep
      | none =>
        simp only at hr1 ⊢
        step with generated.part0.case_1_eo__24mk_5fsymm_spec s1 a0 x hinv1 h64 (hx.grows hg1)
          as ⟨r2, s2, hinv2, hg2, hr2⟩
        cases r2 with
        | Err e =>
          simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg1.trans hg2, trivial⟩
        | Ok o2 =>
          cases o2 with
          | some found =>
            simp only [WP.dspec_ok, WP.uncurry'_pair] at hr2 ⊢
            obtain ⟨t1, t2, rfl, hrep⟩ := hr2
            refine ⟨hinv2, hg1.trans hg2, ?_⟩
            simpa [Eo.__mk_symm] using hrep
          | none =>
            simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair] at hr2 ⊢
            refine ⟨hinv2, hg1.trans hg2, ?_⟩
            have : Eo.__mk_symm x = Eo.Term.Stuck := by
              unfold Eo.__mk_symm
              split
              · exact absurd rfl (hr1 _ _)
              · exact absurd rfl (hr2 _ _)
              · rfl
            rw [this]; exact hinv2.rep_stuck

/-- **`$mk_symm`.** On a store with the invariant and a handle of a term
`x`, the generated program, if it returns, has not panicked, leaves a store
with the invariant in which every earlier handle stands for what it stood
for, and returns a handle of logos's `__mk_symm x` (or an error). -/
theorem generated.part0.eo__24mk_5fsymm_spec (s : Store) (a0 : Term) (x : Eo.Term)
    (hinv : s.Inv) (h64 : Platform64) (hx : s.Rep a0 x) :
    generated.part0.eo__24mk_5fsymm s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__mk_symm x)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.eo__24mk_5fsymm
  apply WP.dspec_mono (Store.framed s hinv (fun s1 => generated.part0.body_eo__24mk_5fsymm s1 a0)
    (fun s' t => s'.Rep t (Eo.__mk_symm x)) (fun _ _ _ hn h => h.congr hn)
    (fun s1 hinv1 hn => by
      apply WP.dspec_mono
        (generated.part0.body_eo__24mk_5fsymm_spec s1 a0 x hinv1 h64 (hx.congr hn))
      rintro ⟨r, s2⟩ h
      cases r <;> simpa [WP.uncurry'_pair] using h))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
