module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
import all CpcMini.SmtEval
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Store.CacheOps
public import PathosProofs.Programs.Frame
public import PathosProofs.Programs.Symm
public import PathosProofs.Programs.Contra

/-!
# `$mk_trans`: a program that is recursive and cached

logos's `__mk_trans t1 t2 tail` walks a conjunction of equalities. The
generated program is four functions that call each other (the program, its
body, the case that recurses and the test of that case's requirement), and
the program looks its arguments up in the cache of results before its body
and keeps the result after it.

The four are proved together, by the induction that their definition as a
fixed point gives: each from what is assumed of the one it calls. The cache
needs its invariant, that an entry is the program's result on its
arguments (`EntryOK`): a result found is right because of it, and a result
kept keeps it.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The shape `(and (= t3 t4) tail)` that the recursive case matches. -/
abbrev transStep (t3 t4 tail : Eo.Term) : Eo.Term :=
  Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.and)
    (Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) t3) t4)) tail

theorem mk_trans_stuck_left (y z : Eo.Term) : Eo.__mk_trans Eo.Term.Stuck y z = Eo.Term.Stuck := by
  simp [Eo.__mk_trans]

theorem mk_trans_stuck_mid (x z : Eo.Term) : Eo.__mk_trans x Eo.Term.Stuck z = Eo.Term.Stuck := by
  unfold Eo.__mk_trans
  split <;> simp_all

theorem mk_trans_step (x y t3 t4 tail : Eo.Term) (hx : x ≠ Eo.Term.Stuck)
    (hy : y ≠ Eo.Term.Stuck) :
    Eo.__mk_trans x y (transStep t3 t4 tail)
      = Eo.__eo_requires y t3 (Eo.__mk_trans x t4 tail) := by
  conv => lhs; unfold Eo.__mk_trans
  split <;> simp_all [transStep]

theorem mk_trans_true (x y : Eo.Term) (hx : x ≠ Eo.Term.Stuck) (hy : y ≠ Eo.Term.Stuck) :
    Eo.__mk_trans x y (Eo.Term.Boolean true)
      = Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) x) y := by
  unfold Eo.__mk_trans
  split <;> simp_all

theorem mk_trans_other (x y z : Eo.Term) (hstep : ∀ t3 t4 tail, z ≠ transStep t3 t4 tail)
    (htrue : z ≠ Eo.Term.Boolean true) : Eo.__mk_trans x y z = Eo.Term.Stuck := by
  unfold Eo.__mk_trans
  split
  · rfl
  · rfl
  · exact absurd rfl (hstep _ _ _)
  · exact absurd rfl htrue
  · rfl

/-- The case that ends the walk: on `true`, `(= t1 t2)`. -/
theorem generated.part0.case_1_eo__24mk_5ftrans_spec (s : Store) (a0 a1 a2 : Term)
    (x y z : Eo.Term) (hinv : s.Inv) (h64 : Platform64)
    (h0 : s.Rep a0 x) (h1 : s.Rep a1 y) (h2 : s.Rep a2 z)
    (hx : x ≠ Eo.Term.Stuck) (hy : y ≠ Eo.Term.Stuck) :
    generated.part0.case_1_eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        z = Eo.Term.Boolean true ∧
          s'.Rep t (Eo.Term.Apply (Eo.Term.Apply (Eo.Term.UOp Eo.UserOp.eq) x) y)
      | core.result.Result.Ok none => z ≠ Eo.Term.Boolean true
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_1_eo__24mk_5ftrans
  step with Store.literal_boolean_spec s true hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok v =>
    simp only at hr ⊢
    rw [Term.ne_eq]
    simp only [Std.bind_ok]
    have hiff := Store.Rep.eq_iff hinv1 (h2.grows hg1) hr
    by_cases hv : a2 = v
    · have hdec : decide (a2 ≠ v) = false := by simp [hv]
      rw [hdec]
      simp only [Bool.false_eq_true, ite_false]
      have hz : z = Eo.Term.Boolean true := hiff.mp hv
      step as ⟨e2, he2⟩
      step with Store.construct_uop_spec s1 Eo.UserOp.eq e2 (by rw [he2]; exact empty_args)
        hinv1 h64 as ⟨r1, s3, hinv3, hg3, hr1⟩
      cases r1 with
      | Err e =>
        simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv3, hg1.trans hg3, trivial⟩
      | Ok v1 =>
        simp only at hr1 ⊢
        step with Store.apply_rep s3 v1 a0 (Eo.Term.UOp Eo.UserOp.eq) x hinv3 h64 hr1
          (h0.grows (hg1.trans hg3)) (by simp) hx as ⟨r2, s4, hinv4, hg4, hr2⟩
        cases r2 with
        | Err e =>
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv4, (hg1.trans hg3).trans hg4, trivial⟩
        | Ok v2 =>
          simp only at hr2 ⊢
          step with Store.apply_rep s4 v2 a1 _ y hinv4 h64 hr2
            (h1.grows ((hg1.trans hg3).trans hg4)) (by simp) hy as ⟨r3, s5, hinv5, hg5, hr3⟩
          cases r3 with
          | Err e =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv5, ((hg1.trans hg3).trans hg4).trans hg5, trivial⟩
          | Ok v3 =>
            simp only [WP.dspec_ok, WP.uncurry'_pair] at hr3 ⊢
            exact ⟨hinv5, ((hg1.trans hg3).trans hg4).trans hg5, hz, hr3⟩
    · have hdec : decide (a2 ≠ v) = true := by simp [hv]
      rw [hdec]
      simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv1, hg1, fun hz => hv (hiff.mpr hz)⟩

/-- What is proved of the program and of its body, for a first argument
`a0`: on handles of `x`, `y` and `z` they return a handle of
`__mk_trans x y z`. -/
def MkTransOK (a0 : Term)
    (f : Store → Term → Term → Result ((core.result.Result Term CheckError) × Store)) : Prop :=
  ∀ (s : Store) (a1 a2 : Term) (x y z : Eo.Term), s.Inv → Platform64 →
    s.Rep a0 x → s.Rep a1 y → s.Rep a2 z →
    f s a1 a2 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__mk_trans x y z)
      | core.result.Result.Err _ => True ⦄div

/-- Of the case that recurses. -/
def MkTransCaseOK (a0 : Term)
    (f : Store → Term → Term →
      Result ((core.result.Result (Option Term) CheckError) × Store)) : Prop :=
  ∀ (s : Store) (a1 a2 : Term) (x y z : Eo.Term), s.Inv → Platform64 →
    s.Rep a0 x → s.Rep a1 y → s.Rep a2 z →
    f s a1 a2 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some t) =>
        ∃ t3 t4 tail, z = transStep t3 t4 tail ∧
          s'.Rep t (Eo.__eo_requires y t3 (Eo.__mk_trans x t4 tail))
      | core.result.Result.Ok none => ∀ t3 t4 tail, z ≠ transStep t3 t4 tail
      | core.result.Result.Err _ => True ⦄div

/-- Of the test of that case's requirement, which makes the recursive call. -/
def MkTransRequiresOK (a0 : Term)
    (f : Store → Term → Term → Term → Term →
      Result ((core.result.Result Term CheckError) × Store)) : Prop :=
  ∀ (s : Store) (a1 v12 v9 v2 : Term) (x y t3 t4 tail : Eo.Term), s.Inv → Platform64 →
    s.Rep a0 x → s.Rep a1 y → s.Rep v12 t3 → s.Rep v9 t4 → s.Rep v2 tail →
    f s a1 v12 v9 v2 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_requires y t3 (Eo.__mk_trans x t4 tail))
      | core.result.Result.Err _ => True ⦄div

theorem requires_ne (y t3 r : Eo.Term) (h : y ≠ t3) : Eo.__eo_requires y t3 r = Eo.Term.Stuck := by
  simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, h]

theorem requires_stuck (t3 r : Eo.Term) :
    Eo.__eo_requires Eo.Term.Stuck t3 r = Eo.Term.Stuck := by
  simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]

theorem requires_eq (y r : Eo.Term) (h : y ≠ Eo.Term.Stuck) : Eo.__eo_requires y y r = r := by
  simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not, h]

set_option maxRecDepth 8000 in
theorem mk_trans_all (a0 : Term) :
    MkTransOK a0 (fun s a1 a2 => generated.part0.eo__24mk_5ftrans s a0 a1 a2) := by
  refine generated.part0.eo__24mk_5ftrans.fixpoint_induct a0
    (MkTransOK a0) (MkTransOK a0) (MkTransCaseOK a0) (MkTransRequiresOK a0)
    (by unfold MkTransOK; prove_adm) (by unfold MkTransOK; prove_adm)
    (by unfold MkTransCaseOK; prove_adm) (by unfold MkTransRequiresOK; prove_adm)
    ?program ?body ?case ?requires
  case program =>
    intro body hbody s a1 a2 x y z hinv h64 h0 h1 h2
    simp only
    step with Store.enter_spec as ⟨r, s1, hn, hh, hs, hc, hl, hd⟩
    have hinv1 : s1.Inv := hinv.congr hn hh hs hc
    cases r with
    | Err e =>
      simp only [WP.dspec_ok, WP.uncurry'_pair] at hd ⊢
      exact ⟨hinv1, ⟨by rw [hn], hl, hd⟩, trivial⟩
    | Ok u =>
      simp only at hd ⊢
      step as ⟨args, hargs⟩
      have hargsv : args.val = [a0, a1, a2] := by rw [hargs]; rfl
      step with Store.cached_program_spec s1 hinv1 58#u32 args as ⟨r1, s3, hinv3, hg3, hn3, hr1⟩
      have hd3 : 0 < s3.depth.val := by rw [hg3.depth, hd]; omega
      have hd3v : s3.depth.val = s.depth.val + 1 := by rw [hg3.depth, hd]
      have hl3 : s3.limits = s.limits := by rw [hg3.limits, hl]
      have hn3' : s3.nodes = s.nodes := by rw [hn3, hn]
      have h0' : s3.Rep a0 x := h0.congr hn3'
      have h1' : s3.Rep a1 y := h1.congr hn3'
      have h2' : s3.Rep a2 z := h2.congr hn3'
      cases r1 with
      | Err error =>
        clear hr1
        dsimp only
        step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hl4, hd4⟩
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv3.congr hn4 hh4 hs4 hc4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_⟩, trivial⟩
        exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
      | Ok o =>
        cases o with
        | some value =>
          have hr1' : ∃ e, e ∈ s1.caches.programs.entries.val ∧ e.program = 58#u32 ∧
              e.args.val = args.val ∧ e.result = value := hr1
          clear hr1
          dsimp only
          obtain ⟨e, he, hep, hea, her⟩ := hr1'
          obtain ⟨b0, b1, b2, x', y', z', hargs', r0, r1', r2, rr⟩ :=
            hinv1.cache.entries e he hep
          have hlist : [b0, b1, b2] = [a0, a1, a2] := by rw [← hargs', hea, hargsv]
          injection hlist with e0 hlist
          injection hlist with e1 hlist
          injection hlist with e2 _
          subst e0; subst e1; subst e2
          have hn1 : s1.nodes.val = s.nodes.val := by rw [hn]
          have hx : x' = x := Rep.functional r0 (by rw [hn1]; exact h0)
          have hy : y' = y := Rep.functional r1' (by rw [hn1]; exact h1)
          have hz : z' = z := Rep.functional r2 (by rw [hn1]; exact h2)
          subst hx; subst hy; subst hz
          have hval : s3.Rep value (Eo.__mk_trans x' y' z') := by
            unfold Store.Rep
            rw [hn3, ← her]; exact rr
          step with Store.leave_spec s3 hd3 as ⟨s4, hn4, hh4, hs4, hc4, hl4, hd4⟩
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv3.congr hn4 hh4 hs4 hc4, ⟨by rw [hn4, hn3'], by rw [hl4, hl3], ?_⟩,
            hval.congr hn4⟩
          exact u32_eq_of_val (by rw [hd4, hd3v]; omega)
        | none =>
          clear hr1
          simp only
          step with hbody s3 a1 a2 x y z hinv3 h64 h0' h1' h2' as ⟨result, s4, hinv4, hg4, hres⟩
          have hd4 : 0 < s4.depth.val := by rw [hg4.depth]; exact hd3
          step with Store.leave_spec s4 hd4 as ⟨s5, hn5, hh5, hs5, hc5, hl5, hd5⟩
          have hinv5 : s5.Inv := hinv4.congr hn5 hh5 hs5 hc5
          have hnodes5 : s.nodes.val <+: s5.nodes.val := by
            rw [hn5, ← hn3']; exact hg4.nodes
          have hl5' : s5.limits = s.limits := by rw [hl5, hg4.limits, hl3]
          have hd5' : s5.depth = s.depth := by
            exact u32_eq_of_val (by rw [hd5, hg4.depth, hd3v]; omega)
          cases result with
          | Err e =>
            simp only [WP.dspec_ok, WP.uncurry'_pair]
            exact ⟨hinv5, ⟨hnodes5, hl5', hd5'⟩, trivial⟩
          | Ok value =>
            simp only at hres ⊢
            have hval5 : s5.Rep value (Eo.__mk_trans x y z) := hres.congr hn5
            step as ⟨args2, hargs2⟩
            have hargs2v : args2.val = [a0, a1, a2] := by rw [hargs2]; rfl
            have hg35 : s3.nodes.val <+: s5.nodes.val := by rw [hn5]; exact hg4.nodes
            step with Store.cache_program_spec s5 hinv5 58#u32 args2 value
              (by
                intro key hkey _
                exact ⟨a0, a1, a2, x, y, z, by rw [hkey, hargs2v], Rep.mono hg35 h0',
                  Rep.mono hg35 h1', Rep.mono hg35 h2', hval5⟩)
              as ⟨r2, s7, hinv7, hg7, hn7⟩
            cases r2 with
            | Err e =>
              simp only [WP.dspec_ok, WP.uncurry'_pair]
              exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
                by rw [hg7.depth, hd5']⟩, trivial⟩
            | Ok u2 =>
              simp only [WP.dspec_ok, WP.uncurry'_pair]
              exact ⟨hinv7, ⟨hnodes5.trans hg7.nodes, by rw [hg7.limits, hl5'],
                by rw [hg7.depth, hd5']⟩, hval5.congr hn7⟩
  case body =>
    intro case0 hcase s a1 a2 x y z hinv h64 h0 h1 h2
    simp only
    rw [h0.is_stuck]
    simp only [Std.bind_ok]
    by_cases hx : x = Eo.Term.Stuck
    · subst hx
      simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      rw [mk_trans_stuck_left]
      exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
    · simp only [hx, decide_false, Bool.false_eq_true, ite_false]
      rw [h1.is_stuck]
      simp only [Std.bind_ok]
      by_cases hy : y = Eo.Term.Stuck
      · subst hy
        simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
          WP.uncurry'_pair]
        rw [mk_trans_stuck_mid]
        exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
      · simp only [hy, decide_false, Bool.false_eq_true, ite_false]
        rw [h2.is_stuck]
        simp only [Std.bind_ok]
        by_cases hz : z = Eo.Term.Stuck
        · subst hz
          simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
            WP.uncurry'_pair]
          rw [mk_trans_other x y _ (by intro _ _ _ h; cases h) (by intro h; cases h)]
          exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
        · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
          step with hcase s a1 a2 x y z hinv h64 h0 h1 h2 as ⟨r3, s1, hinv1, hg1, hr3⟩
          cases r3 with
          | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
          | Ok o3 =>
            cases o3 with
            | some found =>
              simp only [WP.dspec_ok, WP.uncurry'_pair] at hr3 ⊢
              obtain ⟨t3, t4, tail, rfl, hrep⟩ := hr3
              rw [mk_trans_step x y t3 t4 tail hx hy]
              exact ⟨hinv1, hg1, hrep⟩
            | none =>
              simp only at hr3 ⊢
              step with generated.part0.case_1_eo__24mk_5ftrans_spec s1 a0 a1 a2 x y z hinv1 h64
                (h0.grows hg1) (h1.grows hg1) (h2.grows hg1) hx hy as ⟨r4, s2, hinv2, hg2, hr4⟩
              cases r4 with
              | Err e =>
                simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg1.trans hg2, trivial⟩
              | Ok o4 =>
                cases o4 with
                | some found =>
                  simp only [WP.dspec_ok, WP.uncurry'_pair] at hr4 ⊢
                  obtain ⟨rfl, hrep⟩ := hr4
                  rw [mk_trans_true x y hx hy]
                  exact ⟨hinv2, hg1.trans hg2, hrep⟩
                | none =>
                  simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair] at hr4 ⊢
                  rw [mk_trans_other x y z hr3 hr4]
                  exact ⟨hinv2, hg1.trans hg2, hinv2.rep_stuck⟩
  case case =>
    intro req hreq s a1 a2 x y z hinv h64 h0 h1 h2
    simp only
    rcases h2.unapply with ⟨v1, v2, z1, tail, rfl, hv1, hv2, hu⟩ | ⟨hne, hu⟩
    · rw [hu]
      simp only [Std.bind_ok, uncurry_apply_pair]
      rcases hv1.unapply with ⟨v4, v5, w1, w2, rfl, hv4, hv5, hu1⟩ | ⟨hne1, hu1⟩
      · rw [hu1]
        simp only [Std.bind_ok, uncurry_apply_pair]
        step as ⟨e1, he1⟩
        step with Store.construct_uop_spec s Eo.UserOp.and e1 (by rw [he1]; exact empty_args)
          hinv h64 as ⟨r2, s2, hinv2, hg2, hr2⟩
        cases r2 with
        | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg2, trivial⟩
        | Ok v6 =>
          simp only at hr2 ⊢
          rw [Term.ne_eq]
          simp only [Std.bind_ok]
          have hiff := Store.Rep.eq_iff hinv2 (hv4.grows hg2) hr2
          by_cases hv46 : v4 = v6
          · have hdec : decide (v4 ≠ v6) = false := by simp [hv46]
            rw [hdec]
            simp only [Bool.false_eq_true, ite_false]
            have hw1 : w1 = Eo.Term.UOp Eo.UserOp.and := hiff.mp hv46
            subst hw1
            rcases (hv5.grows hg2).unapply with ⟨v8, v9, u1, t4, rfl, hv8, hv9, hu3⟩ | ⟨hne3, hu3⟩
            · rw [hu3]
              simp only [Std.bind_ok, uncurry_apply_pair]
              rcases hv8.unapply with ⟨v11, v12, q1, t3, rfl, hv11, hv12, hu4⟩ | ⟨hne4, hu4⟩
              · rw [hu4]
                simp only [Std.bind_ok, uncurry_apply_pair]
                step as ⟨e3, he3⟩
                step with Store.construct_uop_spec s2 Eo.UserOp.eq e3
                  (by rw [he3]; exact empty_args) hinv2 h64 as ⟨r5, s4, hinv4, hg4, hr5⟩
                cases r5 with
                | Err e =>
                  simp only [WP.dspec_ok, WP.uncurry'_pair]
                  exact ⟨hinv4, hg2.trans hg4, trivial⟩
                | Ok v13 =>
                  simp only at hr5 ⊢
                  rw [Term.ne_eq]
                  simp only [Std.bind_ok]
                  have hiff2 := Store.Rep.eq_iff hinv4 (hv11.grows hg4) hr5
                  by_cases hv1113 : v11 = v13
                  · have hdec2 : decide (v11 ≠ v13) = false := by simp [hv1113]
                    rw [hdec2]
                    simp only [Bool.false_eq_true, ite_false]
                    have hq1 : q1 = Eo.Term.UOp Eo.UserOp.eq := hiff2.mp hv1113
                    subst hq1
                    step with hreq s4 a1 v12 v9 v2 x y t3 t4 tail hinv4 h64
                      (h0.grows (hg2.trans hg4)) (h1.grows (hg2.trans hg4)) (hv12.grows hg4)
                      (hv9.grows hg4) (hv2.grows (hg2.trans hg4)) as ⟨r6, s5, hinv5, hg5, hr6⟩
                    cases r6 with
                    | Err e =>
                      simp only [WP.dspec_ok, WP.uncurry'_pair]
                      exact ⟨hinv5, (hg2.trans hg4).trans hg5, trivial⟩
                    | Ok v14 =>
                      simp only [WP.dspec_ok, WP.uncurry'_pair] at hr6 ⊢
                      exact ⟨hinv5, (hg2.trans hg4).trans hg5, t3, t4, tail, rfl, hr6⟩
                  · have hdec2 : decide (v11 ≠ v13) = true := by simp [hv1113]
                    rw [hdec2]
                    simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
                    refine ⟨hinv4, hg2.trans hg4, ?_⟩
                    intro t3' t4' tail' heq
                    injection heq with heq1 _
                    injection heq1 with _ heq2
                    injection heq2 with heq3 _
                    injection heq3 with heq4 _
                    exact hv1113 (hiff2.mpr heq4)
              · rw [hu4]
                simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
                refine ⟨hinv2, hg2, ?_⟩
                intro t3' t4' tail' heq
                injection heq with heq1 _
                injection heq1 with _ heq2
                injection heq2 with heq3 _
                exact hne4 _ _ heq3
            · rw [hu3]
              simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
              refine ⟨hinv2, hg2, ?_⟩
              intro t3' t4' tail' heq
              injection heq with heq1 _
              injection heq1 with _ heq2
              exact hne3 _ _ heq2
          · have hdec : decide (v4 ≠ v6) = true := by simp [hv46]
            rw [hdec]
            simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
            refine ⟨hinv2, hg2, ?_⟩
            intro t3' t4' tail' heq
            injection heq with heq1 _
            injection heq1 with heq2 _
            exact hv46 (hiff.mpr heq2)
      · rw [hu1]
        simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv, Store.Grows.refl s, ?_⟩
        intro t3' t4' tail' heq
        injection heq with heq1 _
        exact hne1 _ _ heq1
    · rw [hu]
      simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun t3' t4' tail' heq => hne _ _ heq⟩
  case requires =>
    intro prog hprog s a1 v12 v9 v2 x y t3 t4 tail hinv h64 h0 h1 h12 h9 h2
    simp only
    rw [Term.ne_eq]
    simp only [Std.bind_ok]
    have hiff := Store.Rep.eq_iff hinv h1 h12
    by_cases hv : a1 = v12
    · have hdec : decide (a1 ≠ v12) = false := by simp [hv]
      rw [hdec]
      simp only [Bool.false_eq_true, ite_false]
      have hyt : y = t3 := hiff.mp hv
      subst hyt
      rw [h1.is_stuck]
      simp only [Std.bind_ok]
      by_cases hy : y = Eo.Term.Stuck
      · subst hy
        simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
          WP.uncurry'_pair]
        rw [requires_stuck]
        exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩
      · simp only [hy, decide_false, Bool.false_eq_true, ite_false]
        step with hprog s v9 v2 x t4 tail hinv h64 h0 h9 h2 as ⟨r1, s1, hinv1, hg1, hr1⟩
        rw [requires_eq y _ hy]
        cases r1 with
        | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
        | Ok t => simp only [WP.dspec_ok, WP.uncurry'_pair] at hr1 ⊢; exact ⟨hinv1, hg1, hr1⟩
    · have hdec : decide (a1 ≠ v12) = true := by simp [hv]
      rw [hdec]
      simp only [ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      rw [requires_ne y t3 _ (fun h => hv (hiff.mpr h))]
      exact ⟨hinv, Store.Grows.refl s, hinv.rep_stuck⟩

/-- **`$mk_trans`.** On a store with the invariant and handles of `x`, `y`
and `z`, the generated program, if it returns, has not panicked, keeps the
invariant (the cache's with it) and every earlier handle, and returns a
handle of logos's `__mk_trans x y z` (or an error), whether the result
came from the cache or from the body. -/
theorem generated.part0.eo__24mk_5ftrans_spec (s : Store) (a0 a1 a2 : Term) (x y z : Eo.Term)
    (hinv : s.Inv) (h64 : Platform64) (h0 : s.Rep a0 x) (h1 : s.Rep a1 y) (h2 : s.Rep a2 z) :
    generated.part0.eo__24mk_5ftrans s a0 a1 a2 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__mk_trans x y z)
      | core.result.Result.Err _ => True ⦄div :=
  mk_trans_all a0 s a1 a2 x y z hinv h64 h0 h1 h2

end pathos_compiled_checker
