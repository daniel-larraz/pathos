module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Tactic
public import PathosProofs.Programs.Symm

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The first case of `$mk_symm` in the form to be generated. -/
theorem case_0_mk_symm_short (s : Store) (a0 : Term) (x0 : _)
    (hinv : s.Inv) (h64 : Platform64) (h_a0 : Represents.rep s a0 x0) :
    generated.part0.case_0_eo__24mk_5fsymm s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ res, EoCases.__mk_symm.case_0 x0 = some res ∧ Represents.rep s' t res
      | core.result.Result.Ok none => EoCases.__mk_symm.case_0 x0 = none
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_0_eo__24mk_5fsymm
  have hG := Store.Grows.refl s
  pat_unapply h_a0 as ⟨v1, v2, x_v1, x_v2, h_v1, h_v2⟩ else hinv hG in EoCases.__mk_symm.case_0
  pat_unapply h_v1 as ⟨v4, v5, x_v4, x_v5, h_v4, h_v5⟩ else hinv hG in EoCases.__mk_symm.case_0
  obtain ⟨_, hx2ns⟩ := Store.Rep.apply_ne_stuck hinv h_a0
  obtain ⟨_, hy2ns⟩ := Store.Rep.apply_ne_stuck hinv h_v1
  step as ⟨e1, he1⟩
  store_step with Store.construct_uop_spec s Eo.UserOp.eq e1 (by rw [he1]; exact empty_args)
    hinv h64 as ⟨v6, s2, hinv2, h_v6⟩ growing hG carrying h_v2 h_v4 h_v5
  pat_same hv : v4 = v6 from Store.Rep.eq_iff hinv2 h_v4 h_v6 else hinv2 hG
    in EoCases.__mk_symm.case_0
  have hx := (Store.Rep.eq_iff hinv2 h_v4 h_v6).mp hv; subst hx
  step as ⟨e3, he3⟩
  store_step with Store.construct_uop_spec s2 Eo.UserOp.eq e3 (by rw [he3]; exact empty_args)
    hinv2 h64 as ⟨v7, s4, hinv4, h_v7⟩ growing hG carrying h_v2 h_v5
  store_step with Store.apply_rep s4 v7 v2 _ _ hinv4 h64 h_v7 h_v2 (by simp) hx2ns
    as ⟨v8, s5, hinv5, h_v8⟩ growing hG carrying h_v5
  store_step with Store.apply_rep s5 v8 v5 _ _ hinv5 h64 h_v8 h_v5 (by simp) hy2ns
    as ⟨v9, s6, hinv6, h_v9⟩ growing hG
  case_done hinv6 hG with h_v9 in EoCases.__mk_symm.case_0

end pathos_compiled_checker
