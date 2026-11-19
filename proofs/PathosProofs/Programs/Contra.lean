module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
import all CpcMini.SmtEval
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Programs.Frame
public import PathosProofs.Programs.Symm

/-!
# `$eo_prog_contra`: a program with a nonlinear pattern

logos's `__eo_prog_contra` takes two proofs, of `F` and of `(not F)`: the
same `F` twice. The generated code compares the two handles. That this is
the comparison of the two terms is what the store's invariant is for.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The handle `t` stands for the proof `p`: a node `$eo_pf` over a handle
of the proved formula. -/
inductive RepProof (s : Store) : Term → Eo.Proof → Prop where
  | pf (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length → s.data t = TermData.Node schema.Constructor.eo__24eo_5fpf v →
      v.val = [f] → s.Rep f F → RepProof s t (Eo.Proof.pf F)
  | stuck (t : Term) :
      t.val < s.nodes.length → s.data t = TermData.Stuck → RepProof s t Eo.Proof.Stuck

theorem RepProof.congr {s s' : Store} {t : Term} {p : Eo.Proof} (h : RepProof s t p)
    (hn : s'.nodes = s.nodes) : RepProof s' t p := by
  cases h with
  | pf f v F hlt hd hv hf =>
    exact RepProof.pf t f v F (by rw [hn]; exact hlt) (by unfold Store.data; rw [hn]; exact hd) hv
      (hf.congr hn)
  | stuck hlt hd =>
    exact RepProof.stuck t (by rw [hn]; exact hlt) (by unfold Store.data; rw [hn]; exact hd)

/-- `destruct` with `$eo_pf` on a handle of a proof. -/
theorem RepProof.destruct {s : Store} {t : Term} {p : Eo.Proof} (h : RepProof s t p) :
    (∃ f v F, p = Eo.Proof.pf F ∧ v.val = [f] ∧ s.Rep f F ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t
        = ok (core.result.Result.Ok (some v), s)) ∨
    (p = Eo.Proof.Stuck ∧
      Store.destruct s schema.Constructor.eo__24eo_5fpf t = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s _ t rfl]
  cases h with
  | pf f v F hlt hd hv hf =>
    left
    exact ⟨f, v, F, rfl, hv, hf, by simp [hlt, hd]⟩
  | stuck hlt hd =>
    right
    exact ⟨rfl, by simp [hlt, hd]⟩

/-- `literal` with a Boolean gives a handle of it. -/
theorem Store.literal_boolean_spec (s : Store) (b : Bool) (hinv : s.Inv) (h64 : Platform64) :
    Store.literal s (lit.Lit.Boolean b) ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Boolean b)
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.literal
  simp only [Std.bind_ok]
  apply WP.dspec_mono (Store.intern_inv s (TermData.Literal (lit.Lit.Boolean b)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact Rep.boolean t.val b hres.1 hres.2

/-- The case: proofs of `F` and of `(not F)` give `false`. -/
theorem generated.part0.case_0_eo__24eo_5fprog_5fcontra_spec (s : Store) (a0 a1 : Term)
    (p q : Eo.Proof) (hinv : s.Inv) (h64 : Platform64)
    (hp : RepProof s a0 p) (hq : RepProof s a1 q) :
    generated.part0.case_0_eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        (∃ F, p = Eo.Proof.pf F ∧ q = Eo.Proof.pf (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not) F)) ∧
          s'.Rep t (Eo.Term.Boolean false)
      | core.result.Result.Ok none =>
        ¬ ∃ F, p = Eo.Proof.pf F ∧ q = Eo.Proof.pf (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not) F)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_0_eo__24eo_5fprog_5fcontra
  rcases hp.destruct with ⟨f, v, F, rfl, hv, hf, hd⟩ | ⟨rfl, hd⟩
  · rw [hd]
    simp only [Std.bind_ok, uncurry_apply_pair]
    have hvlen : v.length = 1 := by simp [alloc.vec.Vec.length, hv]
    step as ⟨v1, hv1⟩
    have hv1f : v1 = f := by simp [hv1, hv]
    subst hv1f
    rcases hq.destruct with ⟨f1, w, G, rfl, hw, hg, hd1⟩ | ⟨rfl, hd1⟩
    · rw [hd1]
      simp only [Std.bind_ok, uncurry_apply_pair]
      have hwlen : w.length = 1 := by simp [alloc.vec.Vec.length, hw]
      step as ⟨v3, hv3⟩
      have hv3f : v3 = f1 := by simp [hv3, hw]
      subst hv3f
      rcases hg.unapply with ⟨v5, v6, g1, g2, rfl, h5, h6, hu⟩ | ⟨hne, hu⟩
      · rw [hu]
        simp only [Std.bind_ok, uncurry_apply_pair]
        step as ⟨a3, ha3⟩
        step with Store.construct_uop_spec s Eo.UserOp.not a3 (by rw [ha3]; exact empty_args)
          hinv h64 as ⟨r3, s4, hinv4, hg4, hr3⟩
        cases r3 with
        | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv4, hg4, trivial⟩
        | Ok v7 =>
          simp only at hr3 ⊢
          rw [Term.ne_eq]
          simp only [Std.bind_ok]
          have hiff := Store.Rep.eq_iff hinv4 (h5.grows hg4) hr3
          by_cases hv57 : v5 = v7
          · have hdec : decide (v5 ≠ v7) = false := by simp [hv57]
            rw [hdec]
            simp only [Bool.false_eq_true, ite_false]
            have hg1 : g1 = Eo.Term.UOp Eo.UserOp.not := hiff.mp hv57
            subst hg1
            rw [Term.ne_eq]
            simp only [Std.bind_ok]
            have hiff2 := Store.Rep.eq_iff hinv4 (h6.grows hg4) (hf.grows hg4)
            by_cases hv61 : v6 = v1
            · have hdec2 : decide (v6 ≠ v1) = false := by simp [hv61]
              rw [hdec2]
              simp only [Bool.false_eq_true, ite_false]
              have hg2 : g2 = F := hiff2.mp hv61
              subst hg2
              step with Store.literal_boolean_spec s4 false hinv4 h64 as ⟨r4, s5, hinv5, hg5, hr4⟩
              cases r4 with
              | Err e =>
                simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv5, hg4.trans hg5, trivial⟩
              | Ok v8 =>
                simp only [WP.dspec_ok, WP.uncurry'_pair] at hr4 ⊢
                exact ⟨hinv5, hg4.trans hg5, ⟨g2, rfl, rfl⟩, hr4⟩
            · have hdec2 : decide (v6 ≠ v1) = true := by simp [hv61]
              rw [hdec2]
              simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
              refine ⟨hinv4, hg4, ?_⟩
              rintro ⟨F', hF', hq'⟩
              injection hF' with hF'
              injection hq' with hq'
              injection hq' with _ hq'
              exact hv61 (hiff2.mpr (by rw [hq', hF']))
          · have hdec : decide (v5 ≠ v7) = true := by simp [hv57]
            rw [hdec]
            simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv4, hg4, ?_⟩
            rintro ⟨F', _, hq'⟩
            injection hq' with hq'
            injection hq' with hq' _
            exact hv57 (hiff.mpr hq')
      · rw [hu]
        simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv, Store.Grows.refl s, ?_⟩
        rintro ⟨F', _, hq'⟩
        injection hq' with hq'
        exact hne _ _ hq'
    · rw [hd1]
      simp only [Std.bind_ok, uncurry_apply_pair, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      rintro ⟨F', _, hq'⟩
      cases hq'
  · rw [hd]
    simp only [Std.bind_ok, uncurry_apply_pair, WP.dspec_ok, WP.uncurry'_pair]
    refine ⟨hinv, Store.Grows.refl s, ?_⟩
    rintro ⟨F', hF', _⟩
    cases hF'

/-- logos's program on proofs of `F` and `(not F)`. -/
theorem contra_match (F : Eo.Term) (hF : F ≠ Eo.Term.Stuck) :
    Eo.__eo_prog_contra (Eo.Proof.pf F) (Eo.Proof.pf (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not) F))
      = Eo.Term.Boolean false := by
  unfold Eo.__eo_prog_contra
  have heq : Eo.__eo_eq F F = Eo.Term.Boolean true := by
    unfold Eo.__eo_eq
    split
    · exact absurd rfl hF
    · exact absurd rfl hF
    · simp [Eo.native_teq]
  simp [heq, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]

/-- logos's program on anything else. -/
theorem contra_nomatch (p q : Eo.Proof)
    (h : ¬ ∃ F, p = Eo.Proof.pf F ∧ q = Eo.Proof.pf (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.not) F)) :
    Eo.__eo_prog_contra p q = Eo.Term.Stuck := by
  unfold Eo.__eo_prog_contra
  split
  · rename_i F F2
    have hne : F ≠ F2 := by
      intro heq; subst heq; exact h ⟨F, rfl, rfl⟩
    unfold Eo.__eo_eq
    split <;> simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
    exact fun heq => hne heq.symm
  · rfl

theorem generated.part0.body_eo__24eo_5fprog_5fcontra_spec (s : Store) (a0 a1 : Term)
    (p q : Eo.Proof) (hinv : s.Inv) (h64 : Platform64)
    (hp : RepProof s a0 p) (hq : RepProof s a1 q) :
    generated.part0.body_eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_prog_contra p q)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.body_eo__24eo_5fprog_5fcontra
  step with generated.part0.case_0_eo__24eo_5fprog_5fcontra_spec s a0 a1 p q hinv h64 hp hq
    as ⟨r1, s1, hinv1, hg1, hr1⟩
  cases r1 with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok o =>
    cases o with
    | some found =>
      simp only [WP.dspec_ok, WP.uncurry'_pair] at hr1 ⊢
      obtain ⟨⟨F, rfl, rfl⟩, hrep⟩ := hr1
      refine ⟨hinv1, hg1, ?_⟩
      have hF : F ≠ Eo.Term.Stuck := by
        cases hq with
        | pf f v _ hlt hd hv hf => exact (Store.Rep.apply_ne_stuck hinv hf).2
      rw [contra_match F hF]; exact hrep
    | none =>
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair] at hr1 ⊢
      refine ⟨hinv1, hg1, ?_⟩
      rw [contra_nomatch p q hr1]; exact hinv1.rep_stuck

/-- **`$eo_prog_contra`.** On handles of two proofs, the generated program,
if it returns, has not panicked, keeps the store's invariant and every
earlier handle, and returns a handle of logos's `__eo_prog_contra`. -/
theorem generated.part0.eo__24eo_5fprog_5fcontra_spec (s : Store) (a0 a1 : Term)
    (p q : Eo.Proof) (hinv : s.Inv) (h64 : Platform64)
    (hp : RepProof s a0 p) (hq : RepProof s a1 q) :
    generated.part0.eo__24eo_5fprog_5fcontra s a0 a1 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_prog_contra p q)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.eo__24eo_5fprog_5fcontra
  apply WP.dspec_mono (Store.framed s hinv
    (fun s1 => generated.part0.body_eo__24eo_5fprog_5fcontra s1 a0 a1)
    (fun s' t => s'.Rep t (Eo.__eo_prog_contra p q)) (fun _ _ _ hn h => h.congr hn)
    (fun s1 hinv1 hn => by
      apply WP.dspec_mono
        (generated.part0.body_eo__24eo_5fprog_5fcontra_spec s1 a0 a1 p q hinv1 h64
          (hp.congr hn) (hq.congr hn))
      rintro ⟨r, s2⟩ h
      cases r <;> simpa [WP.uncurry'_pair] using h))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
