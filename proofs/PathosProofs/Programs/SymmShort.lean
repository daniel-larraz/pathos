module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Tactic
public import PathosProofs.Programs.Symm

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The first case of `$mk_symm` again, with `store_step`. -/
theorem case_0_mk_symm_short (s : Store) (a0 : Term) (x : Eo.Term)
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
  have hG := Store.Grows.refl s
  rcases hx.unapply with ⟨v1, v2, x1, x2, rfl, h1, h2, hu⟩ | ⟨hne, hu⟩
  · rw [hu]; simp only [Std.bind_ok, uncurry_apply_pair]
    rcases h1.unapply with ⟨v4, v5, y1, y2, rfl, h4, h5, hu1⟩ | ⟨hne1, hu1⟩
    · rw [hu1]; simp only [Std.bind_ok, uncurry_apply_pair]
      obtain ⟨_, hx2ns⟩ := Store.Rep.apply_ne_stuck hinv hx
      obtain ⟨_, hy2ns⟩ := Store.Rep.apply_ne_stuck hinv h1
      step as ⟨e1, he1⟩
      store_step with Store.construct_uop_spec s Eo.UserOp.eq e1 (by rw [he1]; exact empty_args)
        hinv h64 as ⟨v6, s2, hinv2, h6⟩ growing hG carrying h2 h4 h5
      rw [Term.ne_eq]; simp only [Std.bind_ok]
      have hiff := Store.Rep.eq_iff hinv2 h4 h6
      by_cases hv : v4 = v6
      · rw [show decide (v4 ≠ v6) = false by simp [hv]]
        simp only [Bool.false_eq_true, ite_false]
        obtain rfl : y1 = Eo.Term.UOp Eo.UserOp.eq := hiff.mp hv
        step as ⟨e3, he3⟩
        store_step with Store.construct_uop_spec s2 Eo.UserOp.eq e3 (by rw [he3]; exact empty_args)
          hinv2 h64 as ⟨v7, s4, hinv4, h7⟩ growing hG carrying h2 h5
        store_step with Store.apply_rep s4 v7 v2 _ x2 hinv4 h64 h7 h2 (by simp) hx2ns
          as ⟨v8, s5, hinv5, h8⟩ growing hG carrying h5
        store_step with Store.apply_rep s5 v8 v5 _ y2 hinv5 h64 h8 h5 (by simp) hy2ns
          as ⟨v9, s6, hinv6, h9⟩ growing hG
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv6, hG, y2, x2, rfl, h9⟩
      · rw [show decide (v4 ≠ v6) = true by simp [hv]]
        simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv2, hG, ?_⟩
        intro t1 t2 heq
        injection heq with heq1 _
        injection heq1 with heq2 _
        exact hv (hiff.mpr heq2)
    · rw [hu1]; simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, hG, ?_⟩
      intro t1 t2 heq
      injection heq with heq1 _
      exact hne1 _ _ heq1
  · rw [hu]; simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, hG, fun t1 t2 heq => hne _ _ heq⟩

end pathos_compiled_checker
