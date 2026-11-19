module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Programs.Frame
public import PathosProofs.Programs.Symm

/-!
# `$eo_state_is_closed`: a program compiled to a loop

logos's `__eo_state_is_closed` walks the checker's state, a list, and calls
itself on the tail. The generator compiles such a program to a loop: a
`step` function says `Done` with the result or `Again` with the next
argument, and the body repeats it. Aeneas (with `-loops-to-rec`) writes the
loop as a recursive function, and the proof is the induction over it: a
step either gives the result of the whole, or an argument on which the
whole has the same result.

The result is a native Boolean, not a term: a handle whose data is that
Boolean (`NativeBool`).
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- The handle `t` stands for the state object `o`. -/
inductive RepObj (s : Store) : Term → Eo.CStateObj → Prop where
  | assume (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fso_2eassume v →
      v.val = [f] → s.Rep f F → RepObj s t (Eo.CStateObj.assume F)
  | assume_push (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fso_2eassume_5fpush v →
      v.val = [f] → s.Rep f F → RepObj s t (Eo.CStateObj.assume_push F)
  | proven (t f : Term) (v : alloc.vec.Vec Term) (F : Eo.Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fso_2eproven v →
      v.val = [f] → s.Rep f F → RepObj s t (Eo.CStateObj.proven F)

/-- The handle `t` stands for the state `S`. -/
inductive RepState (s : Store) : Term → Eo.CState → Prop where
  | nil (t : Term) (v : alloc.vec.Vec Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fs_2enil v → v.val = [] →
      RepState s t Eo.CState.nil
  | cons (t so tl : Term) (v : alloc.vec.Vec Term) (o : Eo.CStateObj) (S : Eo.CState) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fs_2econs v → v.val = [so, tl] →
      RepObj s so o → RepState s tl S → RepState s t (Eo.CState.cons o S)
  | stuck (t : Term) (v : alloc.vec.Vec Term) :
      t.val < s.nodes.length →
      s.data t = TermData.Node schema.Constructor.eo__24emb_5fs_2eStuck v → v.val = [] →
      RepState s t Eo.CState.Stuck

/-- The handle `t` is the native Boolean `b`. -/
def NativeBool (s : Store) (t : Term) (b : Bool) : Prop :=
  t.val < s.nodes.length ∧ s.data t = TermData.Native (lit.Lit.Boolean b)

theorem Store.data_grows {s s' : Store} (hg : s.nodes.val <+: s'.nodes.val) (t : Term)
    (hlt : t.val < s.nodes.length) : s'.data t = s.data t := by
  obtain ⟨r, hr⟩ := hg
  unfold Store.data
  rw [← hr]; exact getElem!_append_left _ _ _ hlt

theorem Store.lt_grows {s s' : Store} (hg : s.nodes.val <+: s'.nodes.val) {t : Term}
    (hlt : t.val < s.nodes.length) : t.val < s'.nodes.length :=
  Nat.lt_of_lt_of_le hlt hg.length_le

theorem RepObj.mono {s s' : Store} {t : Term} {o : Eo.CStateObj} (h : RepObj s t o)
    (hg : s.nodes.val <+: s'.nodes.val) : RepObj s' t o := by
  cases h with
  | assume f v F hlt hd hv hf =>
    exact RepObj.assume t f v F (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd)
      hv (Rep.mono hg hf)
  | assume_push f v F hlt hd hv hf =>
    exact RepObj.assume_push t f v F (Store.lt_grows hg hlt)
      (by rw [Store.data_grows hg t hlt]; exact hd) hv (Rep.mono hg hf)
  | proven f v F hlt hd hv hf =>
    exact RepObj.proven t f v F (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd)
      hv (Rep.mono hg hf)

theorem RepState.mono {s s' : Store} {t : Term} {S : Eo.CState} (h : RepState s t S)
    (hg : s.nodes.val <+: s'.nodes.val) : RepState s' t S := by
  induction h with
  | nil t v hlt hd hv =>
    exact RepState.nil t v (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd) hv
  | cons t so tl v o S hlt hd hv ho _ ih =>
    exact RepState.cons t so tl v o S (Store.lt_grows hg hlt)
      (by rw [Store.data_grows hg t hlt]; exact hd) hv (ho.mono hg) ih
  | stuck t v hlt hd hv =>
    exact RepState.stuck t v (Store.lt_grows hg hlt) (by rw [Store.data_grows hg t hlt]; exact hd) hv

theorem NativeBool.mono {s s' : Store} {t : Term} {b : Bool} (h : NativeBool s t b)
    (hg : s.nodes.val <+: s'.nodes.val) : NativeBool s' t b :=
  ⟨Store.lt_grows hg h.1, by rw [Store.data_grows hg t h.1]; exact h.2⟩

/-- `tick` counts a step of a loop: the terms are as they were. -/
theorem Store.tick_spec (s : Store) :
    Store.tick s ⦃ r s' =>
      s'.nodes = s.nodes ∧ s'.hashes = s.hashes ∧ s'.slots = s.slots ∧
      s'.caches = s.caches ∧ s'.limits = s.limits ∧ s'.depth = s.depth ⦄ := by
  unfold Store.tick
  split
  · simp
  · step*

/-- `native_bool` gives a handle of the native Boolean. -/
theorem Store.native_bool_spec (s : Store) (b : Bool) (hinv : s.Inv) (h64 : Platform64) :
    native.Store.native_bool s b ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => NativeBool s' t b
      | core.result.Result.Err _ => True ⦄div := by
  unfold native.Store.native_bool Store.raw
  apply WP.dspec_mono (Store.intern_inv s (TermData.Native (lit.Lit.Boolean b)) hinv trivial h64)
  rintro ⟨r, s'⟩ ⟨hinv', hext, hres⟩
  simp only [WP.uncurry'_pair] at hres ⊢
  refine ⟨hinv', hext.grows, ?_⟩
  cases r with
  | Err e => trivial
  | Ok t => exact hres

/-- `destruct` with the constructor of a non-empty state. -/
theorem RepState.destruct_cons {s : Store} {t : Term} {S : Eo.CState} (h : RepState s t S) :
    (∃ so tl v o S', S = Eo.CState.cons o S' ∧ v.val = [so, tl] ∧ RepObj s so o ∧
      RepState s tl S' ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ o S', S ≠ Eo.CState.cons o S') ∧
      Store.destruct s schema.Constructor.eo__24emb_5fs_2econs t
        = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s _ t rfl]
  cases h with
  | nil _ v hlt hd hv => right; exact ⟨(by intro _ _ h; cases h), by simp [hlt, hd]⟩
  | cons _ so tl v o S' hlt hd hv ho hS =>
    left; exact ⟨so, tl, v, o, S', rfl, hv, ho, hS, by simp [hlt, hd]⟩
  | stuck _ v hlt hd hv => right; exact ⟨(by intro _ _ h; cases h), by simp [hlt, hd]⟩

/-- `destruct` with the constructor of a pushed assumption. -/
theorem RepObj.destruct_push {s : Store} {t : Term} {o : Eo.CStateObj} (h : RepObj s t o) :
    (∃ F f v, o = Eo.CStateObj.assume_push F ∧ v.val = [f] ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t
        = ok (core.result.Result.Ok (some v), s)) ∨
    ((∀ F, o ≠ Eo.CStateObj.assume_push F) ∧
      Store.destruct s schema.Constructor.eo__24emb_5fso_2eassume_5fpush t
        = ok (core.result.Result.Ok none, s)) := by
  rw [Store.destruct_data_eq s _ t rfl]
  cases h with
  | assume f v F hlt hd hv hf => right; exact ⟨(by intro _ h; cases h), by simp [hlt, hd]⟩
  | assume_push f v F hlt hd hv hf => left; exact ⟨F, f, v, rfl, hv, by simp [hlt, hd]⟩
  | proven f v F hlt hd hv hf => right; exact ⟨(by intro _ h; cases h), by simp [hlt, hd]⟩

/-- First case: a state that begins with a pushed assumption is not closed. -/
theorem generated.part0.case_0_eo__24eo_5fstate_5fis_5fclosed_spec (s : Store) (a0 : Term)
    (S : Eo.CState) (hinv : s.Inv) (h64 : Platform64) (hS : RepState s a0 S) :
    generated.part0.case_0_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some n) =>
        (∃ F S', S = Eo.CState.cons (Eo.CStateObj.assume_push F) S') ∧
          ∃ t, n = Next.Done t ∧ NativeBool s' t false
      | core.result.Result.Ok none =>
        ∀ F S', S ≠ Eo.CState.cons (Eo.CStateObj.assume_push F) S'
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_0_eo__24eo_5fstate_5fis_5fclosed
  rcases hS.destruct_cons with ⟨so, tl, v, o, S', rfl, hv, ho, hS', hd⟩ | ⟨hne, hd⟩
  · rw [hd]
    simp only [Std.bind_ok, uncurry_apply_pair]
    have hvlen : v.length = 2 := by simp [alloc.vec.Vec.length, hv]
    step as ⟨v1, hv1⟩
    have hv1so : v1 = so := by simp [hv1, hv]
    subst hv1so
    step as ⟨v2, hv2⟩
    rcases ho.destruct_push with ⟨F, f, w, rfl, hw, hd1⟩ | ⟨hne1, hd1⟩
    · rw [hd1]
      simp only [Std.bind_ok, uncurry_apply_pair]
      have hwlen : w.length = 1 := by simp [alloc.vec.Vec.length, hw]
      step as ⟨v4, hv4⟩
      step with Store.native_bool_spec s false hinv h64 as ⟨r2, s3, hinv3, hg3, hr2⟩
      cases r2 with
      | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv3, hg3, trivial⟩
      | Ok v3 =>
        simp only [WP.dspec_ok, WP.uncurry'_pair] at hr2 ⊢
        exact ⟨hinv3, hg3, ⟨F, S', rfl⟩, v3, rfl, hr2⟩
    · rw [hd1]
      simp only [Std.bind_ok, uncurry_apply_pair, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      intro F S'' heq
      injection heq with heq1 _
      exact hne1 F heq1
  · rw [hd]
    simp only [Std.bind_ok, uncurry_apply_pair, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, fun F S' heq => hne _ _ heq⟩

/-- Second case: any other non-empty state is closed if its tail is. -/
theorem generated.part0.case_1_eo__24eo_5fstate_5fis_5fclosed_spec (s : Store) (a0 : Term)
    (S : Eo.CState) (hinv : s.Inv) (hS : RepState s a0 S) :
    generated.part0.case_1_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some n) =>
        ∃ o S' tl arr, S = Eo.CState.cons o S' ∧ n = Next.Again arr ∧ arr.val = [tl] ∧
          RepState s' tl S'
      | core.result.Result.Ok none => ∀ o S', S ≠ Eo.CState.cons o S'
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_1_eo__24eo_5fstate_5fis_5fclosed
  rcases hS.destruct_cons with ⟨so, tl, v, o, S', rfl, hv, ho, hS', hd⟩ | ⟨hne, hd⟩
  · rw [hd]
    simp only [Std.bind_ok, uncurry_apply_pair]
    have hvlen : v.length = 2 := by simp [alloc.vec.Vec.length, hv]
    step as ⟨v1, hv1⟩
    step as ⟨v2, hv2⟩
    have hv2tl : v2 = tl := by simp [hv2, hv]
    subst hv2tl
    simp only [WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, o, S', v2, _, rfl, rfl, rfl, hS'⟩
  · rw [hd]
    simp only [Std.bind_ok, uncurry_apply_pair, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, fun o S' heq => hne _ _ heq⟩

/-- Third case: the empty state is closed. -/
theorem generated.part0.case_2_eo__24eo_5fstate_5fis_5fclosed_spec (s : Store) (a0 : Term)
    (S : Eo.CState) (hinv : s.Inv) (h64 : Platform64) (hS : RepState s a0 S) :
    generated.part0.case_2_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some n) =>
        S = Eo.CState.nil ∧ ∃ t, n = Next.Done t ∧ NativeBool s' t true
      | core.result.Result.Ok none => S ≠ Eo.CState.nil
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_2_eo__24eo_5fstate_5fis_5fclosed
  step as ⟨e1, he1⟩
  step with Store.construct_data_spec s schema.Constructor.eo__24emb_5fs_2enil e1 hinv h64 rfl
    as ⟨r, s2, hinv2, hext, hr⟩
  have hg2 := hext.grows
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg2, trivial⟩
  | Ok v =>
    simp only at hr ⊢
    obtain ⟨hvlt, vv, hvv, hvd⟩ := hr
    have hvv' : vv.val = [] := by rw [hvv, he1]; exact empty_args
    have hS2 := hS.mono hg2.nodes
    rw [Term.ne_eq]
    simp only [Std.bind_ok]
    by_cases hv : a0 = v
    · have hdec : decide (a0 ≠ v) = false := by simp [hv]
      rw [hdec]
      simp only [Bool.false_eq_true, ite_false]
      have hnil : S = Eo.CState.nil := by
        subst hv
        cases hS2 with
        | nil _ w hlt hd hw => rfl
        | cons _ so tl w o S' hlt hd hw ho hS' => rw [hvd] at hd; injection hd with h1 _; cases h1
        | stuck _ w hlt hd hw => rw [hvd] at hd; injection hd with h1 _; cases h1
      step with Store.native_bool_spec s2 true hinv2 h64 as ⟨r1, s3, hinv3, hg3, hr1⟩
      cases r1 with
      | Err e =>
        simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv3, hg2.trans hg3, trivial⟩
      | Ok v1 =>
        simp only [WP.dspec_ok, WP.uncurry'_pair] at hr1 ⊢
        exact ⟨hinv3, hg2.trans hg3, hnil, v1, rfl, hr1⟩
    · have hdec : decide (a0 ≠ v) = true := by simp [hv]
      rw [hdec]
      simp only [ite_true, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv2, hg2, ?_⟩
      intro hnil
      subst hnil
      cases hS2 with
      | nil _ w hlt hd hw =>
        have hw' : w = vv := alloc.vec.Vec.ext _ _ (by rw [hw, hvv'])
        subst hw'
        have := hinv2.table.nodup a0.val v.val hlt hvlt (by
          have h1 : s2.nodes.val[a0.val]! = s2.data a0 := rfl
          have h2 : s2.nodes.val[v.val]! = s2.data v := rfl
          rw [h1, h2, hd, hvd])
        exact hv (u32_eq_of_val this)

/-- Last case: anything else is not closed. -/
theorem generated.part0.case_3_eo__24eo_5fstate_5fis_5fclosed_spec (s : Store) (a0 : Term)
    (hinv : s.Inv) (h64 : Platform64) :
    generated.part0.case_3_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some n) => ∃ t, n = Next.Done t ∧ NativeBool s' t false
      | core.result.Result.Ok none => False
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.case_3_eo__24eo_5fstate_5fis_5fclosed
  step with Store.native_bool_spec s false hinv h64 as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok v =>
    simp only [WP.dspec_ok, WP.uncurry'_pair] at hr ⊢
    exact ⟨hinv1, hg1, v, rfl, hr⟩

/-- What a step answers: the result of the whole, or a state on which the
whole has the same result. -/
def ClosedNext (s' : Store) (S : Eo.CState) : Next (Array Term 1#usize) → Prop
  | Next.Done t => NativeBool s' t (Eo.__eo_state_is_closed S)
  | Next.Again arr => ∃ tl S', arr.val = [tl] ∧ RepState s' tl S' ∧
      Eo.__eo_state_is_closed S = Eo.__eo_state_is_closed S'

theorem generated.part0.step_eo__24eo_5fstate_5fis_5fclosed_spec (s : Store) (a0 : Term)
    (S : Eo.CState) (hinv : s.Inv) (h64 : Platform64) (hS : RepState s a0 S) :
    generated.part0.step_eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok n => ClosedNext s' S n
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.step_eo__24eo_5fstate_5fis_5fclosed
  step with Store.tick_spec as ⟨r, s1, hn, hh, hs, hc, hl, hd⟩
  have hinv1 : s1.Inv := hinv.congr hn hh hs hc
  have hg1 : s.Grows s1 := ⟨by rw [hn], hl, hd⟩
  have hS1 : RepState s1 a0 S := hS.mono hg1.nodes
  cases r with
  | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
  | Ok u =>
    simp only
    step with generated.part0.case_0_eo__24eo_5fstate_5fis_5fclosed_spec s1 a0 S hinv1 h64 hS1
      as ⟨r1, s2, hinv2, hg2, hr1⟩
    cases r1 with
    | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv2, hg1.trans hg2, trivial⟩
    | Ok o1 =>
      cases o1 with
      | some found =>
        simp only [WP.dspec_ok, WP.uncurry'_pair] at hr1 ⊢
        obtain ⟨⟨F, S', rfl⟩, t, rfl, hb⟩ := hr1
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        show NativeBool s2 t (Eo.__eo_state_is_closed _)
        simpa [Eo.__eo_state_is_closed] using hb
      | none =>
        simp only at hr1 ⊢
        step with generated.part0.case_1_eo__24eo_5fstate_5fis_5fclosed_spec s2 a0 S hinv2
          (hS1.mono hg2.nodes) as ⟨r2, s3, hinv3, hg3, hr2⟩
        cases r2 with
        | Err e =>
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          exact ⟨hinv3, (hg1.trans hg2).trans hg3, trivial⟩
        | Ok o2 =>
          cases o2 with
          | some found =>
            simp only [WP.dspec_ok, WP.uncurry'_pair] at hr2 ⊢
            obtain ⟨o, S', tl, arr, rfl, rfl, harr, htl⟩ := hr2
            refine ⟨hinv3, (hg1.trans hg2).trans hg3, tl, S', harr, htl, ?_⟩
            cases o with
            | assume_push F => exact absurd rfl (hr1 F S')
            | assume F => simp [Eo.__eo_state_is_closed]
            | proven F => simp [Eo.__eo_state_is_closed]
          | none =>
            simp only at hr2 ⊢
            step with generated.part0.case_2_eo__24eo_5fstate_5fis_5fclosed_spec s3 a0 S hinv3 h64
              ((hS1.mono hg2.nodes).mono hg3.nodes) as ⟨r3, s4, hinv4, hg4, hr3⟩
            cases r3 with
            | Err e =>
              simp only [WP.dspec_ok, WP.uncurry'_pair]
              exact ⟨hinv4, ((hg1.trans hg2).trans hg3).trans hg4, trivial⟩
            | Ok o3 =>
              cases o3 with
              | some found =>
                simp only [WP.dspec_ok, WP.uncurry'_pair] at hr3 ⊢
                obtain ⟨rfl, t, rfl, hb⟩ := hr3
                refine ⟨hinv4, ((hg1.trans hg2).trans hg3).trans hg4, ?_⟩
                show NativeBool s4 t (Eo.__eo_state_is_closed _)
                simpa [Eo.__eo_state_is_closed] using hb
              | none =>
                simp only at hr3 ⊢
                step with generated.part0.case_3_eo__24eo_5fstate_5fis_5fclosed_spec s4 a0 hinv4
                  h64 as ⟨r4, s5, hinv5, hg5, hr4⟩
                cases r4 with
                | Err e =>
                  simp only [WP.dspec_ok, WP.uncurry'_pair]
                  exact ⟨hinv5, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, trivial⟩
                | Ok o4 =>
                  cases o4 with
                  | some found =>
                    simp only [WP.dspec_ok, WP.uncurry'_pair] at hr4 ⊢
                    obtain ⟨t, rfl, hb⟩ := hr4
                    refine ⟨hinv5, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, ?_⟩
                    show NativeBool s5 t (Eo.__eo_state_is_closed S)
                    have : Eo.__eo_state_is_closed S = false := by
                      cases S with
                      | nil => exact absurd rfl hr3
                      | cons o S' => exact absurd rfl (hr2 o S')
                      | Stuck => simp [Eo.__eo_state_is_closed]
                    rw [this]; exact hb
                  | none => exact absurd hr4 (by simp)

/-- The loop: by induction over it, a step either ends it with the result
or goes on with a state that has the same result. -/
theorem generated.part0.body_eo__24eo_5fstate_5fis_5fclosed_loop_spec (a0 : Term) (s : Store)
    (S : Eo.CState) (hinv : s.Inv) (h64 : Platform64) (hS : RepState s a0 S) :
    generated.part0.body_eo__24eo_5fstate_5fis_5fclosed_loop a0 s ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => NativeBool s' t (Eo.__eo_state_is_closed S)
      | core.result.Result.Err _ => True ⦄div := by
  revert a0 s S
  apply generated.part0.body_eo__24eo_5fstate_5fis_5fclosed_loop.fixpoint_induct
    (motive := fun f => ∀ (a0 : Term) (s : Store) (S : Eo.CState), s.Inv →
      RepState s a0 S →
      f a0 s ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok t => NativeBool s' t (Eo.__eo_state_is_closed S)
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih a0 s S hinv hS
    simp only
    step with generated.part0.step_eo__24eo_5fstate_5fis_5fclosed_spec s a0 S hinv h64 hS
      as ⟨r, s1, hinv1, hg1, hr⟩
    cases r with
    | Err e => simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨hinv1, hg1, trivial⟩
    | Ok n =>
      cases n with
      | Done value =>
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, hr⟩
      | Again next =>
        obtain ⟨tl, S', hnext, htl, heq⟩ := hr
        simp only
        have hlen : next.length = 1 := by simp [Array.length, hnext]
        step as ⟨a01, ha01⟩
        have : a01 = tl := by simp [ha01, hnext]
        subst this
        apply WP.dspec_mono (ih a01 s1 S' hinv1 htl)
        rintro ⟨r', s'⟩ ⟨hinv', hg', hres⟩
        simp only [WP.uncurry'_pair] at hres ⊢
        refine ⟨hinv', hg1.trans hg', ?_⟩
        cases r' with
        | Err e => trivial
        | Ok t => simp only at hres ⊢; rw [heq]; exact hres

theorem NativeBool.congr {s s' : Store} {t : Term} {b : Bool} (h : NativeBool s t b)
    (hn : s'.nodes = s.nodes) : NativeBool s' t b := by
  unfold NativeBool Store.data at h ⊢
  rw [hn]; exact h

theorem RepState.congr {s s' : Store} {t : Term} {S : Eo.CState} (h : RepState s t S)
    (hn : s'.nodes = s.nodes) : RepState s' t S :=
  h.mono (by rw [hn])

/-- **`$eo_state_is_closed`.** On a handle of a state, the generated
program, if it returns, has not panicked, keeps the store's invariant and
every earlier handle, and returns the native Boolean that logos's
`__eo_state_is_closed` gives (or an error). -/
theorem generated.part0.eo__24eo_5fstate_5fis_5fclosed_spec (s : Store) (a0 : Term)
    (S : Eo.CState) (hinv : s.Inv) (h64 : Platform64) (hS : RepState s a0 S) :
    generated.part0.eo__24eo_5fstate_5fis_5fclosed s a0 ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => NativeBool s' t (Eo.__eo_state_is_closed S)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.eo__24eo_5fstate_5fis_5fclosed
  apply WP.dspec_mono (Store.framed s hinv
    (fun s1 => generated.part0.body_eo__24eo_5fstate_5fis_5fclosed s1 a0)
    (fun s' t => NativeBool s' t (Eo.__eo_state_is_closed S)) (fun _ _ _ hn h => h.congr hn)
    (fun s1 hinv1 hn => by
      apply WP.dspec_mono
        (generated.part0.body_eo__24eo_5fstate_5fis_5fclosed_loop_spec a0 s1 S hinv1 h64
          (hS.congr hn))
      rintro ⟨r, s2⟩ h
      cases r <;> simpa [WP.uncurry'_pair] using h))
  rintro ⟨r, s'⟩ h
  cases r <;> simpa [WP.uncurry'_pair] using h

end pathos_compiled_checker
